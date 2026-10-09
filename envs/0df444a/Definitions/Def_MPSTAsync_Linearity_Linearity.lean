-- Prove2me | Definitions.Def_MPSTAsync_Linearity_Linearity
-- name    : MPSTAsync_Linearity_Linearity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T23:06:50.888515+00:00
-- url     : https://prove2.me/theorems/2e1b1f44-dd8d-4efc-9bcf-ce147e5bd7fd
-- title:
--   Defs. 3.3, 3.7, 3.11, 3.12 — action nodes, order, dependencies and linearity
-- statement:
--   An **action node** is a position of a communication or branching in the finite unfolding of a global type. Its label records the sender, receiver, and session channel index. The **action order** $\prec$ relates an action to actions inside its continuation or a selected branch, propagates those relations through surrounding syntax, and is transitively closed. Actions in separate parallel components or separate branches are unordered.
--
--   The immediate dependency relations compare ordered actions: II means the receivers agree, IO means the first receiver is the second sender, and OO means the senders and channel indices agree. An input dependency is a chain of zero or more IO steps followed by one II step; an output dependency is a nonempty chain of OO or IO steps. A global type is **linear** when every ordered pair of actions on the same channel has both kinds of dependency, and the same condition holds for every global type it carries:
--
--   $$
--   \operatorname{Linear}(G)\iff\operatorname{MainLinear}(G)\;\land\;\text{all carried global types satisfy the same condition}.
--   $$
--
--   This definition is the central safety condition used by the paper's later typing results.
--
--   **Formalization Note** Positions are lists of natural-number child indices. Branches are lists, and `WellFormed` records nonempty distinct-label branches, closed guarded recursion, distinct sender and receiver, and positive one-based channel indices. The input-chain lower bound is one: the printed $n\ge0$ is incompatible with its required final II step. The transitive carried-type relation includes shared global types inside located end-point types.
-- source:
--   Honda, Yoshida, Carbone, Multiparty Asynchronous Session Types, J. ACM 63(1) (2016), Art. 9, pp. 15–16, 19–20, Defs. 3.3, 3.7, 3.11, 3.12; https://doi.org/10.1145/2827695

import Mathlib
import Definitions.Def_MPSTAsync_Linearity_GlobalTypes

namespace MPSTAsync.Linearity

abbrev Position := List ℕ

/- Positions include the syntactic root. A communication has child 0, a
   branching has one child per list entry, and parallel has children 0 and 1. -/
def subterm : GType → Position → Option GType
  | G, [] => some G
  | .comm _ _ _ _ G, 0 :: π => subterm G π
  | .branch _ _ _ bs, i :: π => (bs[i]?).bind (fun b => subterm b.2 π)
  | .par G _, 0 :: π => subterm G π
  | .par _ H, 1 :: π => subterm H π
  | .mu _ G, 0 :: π => subterm G π
  | _, _ => none

def label (G : GType) (π : Position) : Option (Role × Role × ℕ) :=
  match subterm G π with
  | some (.comm p q k _ _) => some (p, q, k)
  | some (.branch p q k _) => some (p, q, k)
  | _ => none

def IsNode (G : GType) (π : Position) : Prop := (label G π).isSome

/- The five generators of Definition 3.7, before transitive closure. -/
inductive PrecStep : GType → Position → Position → Prop where
  | commRoot {p q k U G π} : IsNode G π →
      PrecStep (.comm p q k U G) [] (0 :: π)
  | branchRoot {p q k bs i l G π} : bs[i]? = some (l, G) → IsNode G π →
      PrecStep (.branch p q k bs) [] (i :: π)
  | commTail {p q k U G π ρ} : PrecStep G π ρ →
      PrecStep (.comm p q k U G) (0 :: π) (0 :: ρ)
  | branchTail {p q k bs i l G π ρ} : bs[i]? = some (l, G) →
      PrecStep G π ρ → PrecStep (.branch p q k bs) (i :: π) (i :: ρ)
  | parLeft {G H π ρ} : PrecStep G π ρ →
      PrecStep (.par G H) (0 :: π) (0 :: ρ)
  | parRight {G H π ρ} : PrecStep H π ρ →
      PrecStep (.par G H) (1 :: π) (1 :: ρ)

def Prec (G : GType) (π ρ : Position) : Prop :=
  Relation.TransGen (PrecStep G) π ρ

def PrecII (G : GType) (π ρ : Position) : Prop :=
  Prec G π ρ ∧ ∃ p₁ p₂ q k₁ k₂,
    label G π = some (p₁, q, k₁) ∧ label G ρ = some (p₂, q, k₂)

def PrecIO (G : GType) (π ρ : Position) : Prop :=
  Prec G π ρ ∧ ∃ p q r k₁ k₂,
    label G π = some (p, q, k₁) ∧ label G ρ = some (q, r, k₂)

def PrecOO (G : GType) (π ρ : Position) : Prop :=
  Prec G π ρ ∧ ∃ p q₁ q₂ k,
    label G π = some (p, q₁, k) ∧ label G ρ = some (p, q₂, k)

/- Zero or more IO edges followed by one II edge. -/
def InputDep (G : GType) (π ρ : Position) : Prop :=
  ∃ σ, Relation.ReflTransGen (PrecIO G) π σ ∧ PrecII G σ ρ

/- A nonempty chain of OO or IO edges. -/
def OutputDep (G : GType) (π ρ : Position) : Prop :=
  Relation.TransGen (fun a b => PrecOO G a b ∨ PrecIO G a b) π ρ

/- A shared global type can occur in a value sort or inside an endpoint type. -/
mutual
inductive SharedInE : EType → GType → Prop where
  | sendValue {k U T H} : SharedInV U H → SharedInE (.send k U T) H
  | sendTail {k U T H} : SharedInE T H → SharedInE (.send k U T) H
  | recvValue {k U T H} : SharedInV U H → SharedInE (.recv k U T) H
  | recvTail {k U T H} : SharedInE T H → SharedInE (.recv k U T) H
  | selBranch {k bs l T H} : (l, T) ∈ bs → SharedInE T H → SharedInE (.sel k bs) H
  | braBranch {k bs l T H} : (l, T) ∈ bs → SharedInE T H → SharedInE (.bra k bs) H
  | muBody {t T H} : SharedInE T H → SharedInE (.mu t T) H
inductive SharedInV : VType → GType → Prop where
  | sort {Ss H} : SType.shared H ∈ Ss → SharedInV (.sorts Ss) H
  | located {T p H} : SharedInE T H → SharedInV (.located T p) H
end

inductive DirectCarried : GType → GType → Prop where
  | commValue {p q k U G H} : SharedInV U H → DirectCarried (.comm p q k U G) H
  | commTail {p q k U G H} : DirectCarried G H → DirectCarried (.comm p q k U G) H
  | branchBody {p q k bs l G H} : (l, G) ∈ bs → DirectCarried G H →
      DirectCarried (.branch p q k bs) H
  | parLeft {G₁ G₂ H} : DirectCarried G₁ H → DirectCarried (.par G₁ G₂) H
  | parRight {G₁ G₂ H} : DirectCarried G₂ H → DirectCarried (.par G₁ G₂) H
  | muBody {t G H} : DirectCarried G H → DirectCarried (.mu t G) H

def Carried (G H : GType) : Prop := Relation.TransGen DirectCarried G H

/- Global types in the paper are closed and contractive; their branch families
   are nonempty with different labels, their roles differ, and indices are
   1-based. Carried global types satisfy the same conditions. -/
inductive ClosedAt : List TVar → GType → Prop where
  | comm {Γ p q k U G} : ClosedAt Γ G → ClosedAt Γ (.comm p q k U G)
  | branch {Γ p q k bs} : (∀ b ∈ bs, ClosedAt Γ b.2) → ClosedAt Γ (.branch p q k bs)
  | par {Γ G H} : ClosedAt Γ G → ClosedAt Γ H → ClosedAt Γ (.par G H)
  | mu {Γ t G} : ClosedAt (t :: Γ) G → ClosedAt Γ (.mu t G)
  | var {Γ t} : t ∈ Γ → ClosedAt Γ (.var t)
  | stop {Γ} : ClosedAt Γ .stop

def Guarded (t : TVar) : GType → Prop
  | .comm .. => True
  | .branch .. => True
  | .par G H => Guarded t G ∧ Guarded t H
  | .mu u G => u = t ∨ Guarded t G
  | .var u => u ≠ t
  | .stop => True

inductive Contractive : GType → Prop where
  | comm {p q k U G} : Contractive G → Contractive (.comm p q k U G)
  | branch {p q k bs} : (∀ b ∈ bs, Contractive b.2) →
      Contractive (.branch p q k bs)
  | par {G H} : Contractive G → Contractive H → Contractive (.par G H)
  | mu {t G} : Guarded t G → Contractive G → Contractive (.mu t G)
  | var {t} : Contractive (.var t)
  | stop : Contractive .stop

inductive Shape : GType → Prop where
  | comm {p q k U G} : p ≠ q → 0 < k → Shape G → Shape (.comm p q k U G)
  | branch {p q k bs} : p ≠ q → 0 < k → bs ≠ [] →
      (bs.map Prod.fst).Nodup → (∀ b ∈ bs, Shape b.2) →
      Shape (.branch p q k bs)
  | par {G H} : Shape G → Shape H → Shape (.par G H)
  | mu {t G} : Shape G → Shape (.mu t G)
  | var {t} : Shape (.var t)
  | stop : Shape .stop

def WellFormedCore (G : GType) : Prop := ClosedAt [] G ∧ Contractive G ∧ Shape G

def WellFormed (G : GType) : Prop :=
  WellFormedCore G ∧ ∀ H, Carried G H → WellFormedCore H

def MainLinear (G : GType) : Prop :=
  ∀ π ρ p₁ q₁ p₂ q₂ k,
    Prec G π ρ →
    label G π = some (p₁, q₁, k) →
    label G ρ = some (p₂, q₂, k) →
    InputDep G π ρ ∧ OutputDep G π ρ

/- Definition 3.12 applies the same constraint recursively to every carried global
   type. The transitive closure of DirectCarried covers arbitrarily nested carriers. -/
def Linear (G : GType) : Prop :=
  MainLinear G ∧ ∀ H, Carried G H → ∀ n, MainLinear (unfold n H)

def IsLinear (G : GType) : Prop := ∀ n, Linear (unfold n G)

end MPSTAsync.Linearity


