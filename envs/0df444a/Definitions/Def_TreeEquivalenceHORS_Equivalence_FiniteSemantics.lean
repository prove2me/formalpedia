-- Prove2me | Definitions.Def_TreeEquivalenceHORS_Equivalence_FiniteSemantics
-- name    : TreeEquivalenceHORS_Equivalence_FiniteSemantics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:43:13.699222+00:00
-- url     : https://prove2.me/theorems/f994d142-52b1-4e93-befd-99dcf45eefc5
-- title:
--   Finite monotone semantics, least fixed point $\eta^*$, the exact reader and exact prefixes
-- statement:
--   1. **Domains.** $D_o=\{0<1\}$ and $D_{\sigma\to\tau}$ is the finite poset of monotone maps $D_\sigma\to D_\tau$, ordered pointwise, with least element the constant-$\bot$ map. Domains are enumerated finite tables (Section 6.2): an element of $D_{\sigma\to\tau}$ is the list of its values at the enumerated elements of $D_\sigma$.
--   2. **Denotation** (Equation (27)). $[\![x]\!]_{\eta,\rho}=\rho(x)$, $[\![F]\!]_{\eta,\rho}=\eta(F)$, $[\![a]\!]_{\eta,\rho}=\lambda d_1\cdots d_r.\,1$ for $a:o^r\to o$, and $[\![t\,u]\!]_{\eta,\rho}=[\![t]\!]_{\eta,\rho}([\![u]\!]_{\eta,\rho})$.
--   3. **Fixed point.** $\Phi_G(\eta)(F)(\vec v)=[\![t_F]\!]_{\eta,\rho_{\vec v}}$ updates all nonterminals simultaneously. From the all-bottom environment $\eta_0$, $\eta^*=\eta_B=\Phi_G^B(\eta_0)$ with $B=|E_G|=\prod_F|D_{\tau_F}|$.
--   4. **Reader** (Section 6.4). $\mathrm{head}_G(t)$ returns $\bot$ if $[\![t]\!]_{\eta^*}=0$; otherwise it searches increasing head-unfolding budgets until a terminal application is exposed and returns it. $\mathrm{read}_G(t,\varepsilon)$ is that label or $\bot$; $\mathrm{read}_G(t,iw')=\mathrm{read}_G(u_i,w')$ if $\mathrm{head}_G(t)=a(\vec u)$ and $i<|\vec u|$, and $\dagger$ otherwise.
--   5. **Prefixes.** With $b$ the maximal terminal arity ($0$ for an empty alphabet), $\mathrm{Pref}(G,t,d)$ lists the label, $\bot$ or absence of $\mathrm{BT}_G(t)$ at every word over $\{0,\dots,b-1\}$ of length strictly less than $d$, in a fixed order.
--
--   This is the effective side of the upper bound of Section 6.
--
--   **Formalization Note** The search is a Mathlib partial computation (`Nat.rfind`), so the reader is `Part`-valued and its termination is a theorem (Lemma 6.2), not an assumption. `Pref` is defined from the value tree; its computability is the content of Lemma 6.2.
-- source:
--   Mingkun Xiao, Yixuan Sun, Tree Equivalence of Higher-Order Recursion Schemes Is Undecidable, STOC 2027 submission #421 (October 2026), source.pdf SHA-256 e875d09ced029e3f5cb114abba049e4a2b1bdaa9b064c98b0d71f2ec7451c7af, Section 6.1–6.4, Equation (27), printed pp. 22–25 / PDF pp. 24–27

import Mathlib
import Definitions.Def_TreeEquivalenceHORS_Equivalence_Semantics

namespace TreeEquivalenceHORS.Equivalence

/-! # Finite monotone semantics, the exact reader and prefixes (Section 6; PDF pp. 24–27)

The domains `D_o = {0 < 1}` and `D_{σ→τ}` (monotone maps, ordered pointwise) are represented by
enumerated finite tables as in Section 6.2: an element of `D_{σ→τ}` is the list of its values at
the elements of `D_σ`, in the enumeration order of `D_σ`. -/

/-- Table values: `bit b` at ground type (`false = 0`, `true = 1`), `tab l` at a function type. -/
inductive SVal : Type where
  | bit (b : Bool) : SVal
  | tab (l : List SVal) : SVal
  deriving Inhabited

/-- The pointwise order of `D_σ` on table representations. -/
def leT : Ty → SVal → SVal → Bool
  | .o, .bit a, .bit b => !a || b
  | .arr _ τ, .tab l₁, .tab l₂ =>
      l₁.length == l₂.length && (List.zip l₁ l₂).all fun p => leT τ p.1 p.2
  | _, _, _ => false

/-- All lists of length `k` with entries from `L`. -/
def tuples {α : Type} : ℕ → List α → List (List α)
  | 0, _ => [[]]
  | k + 1, L => L.flatMap fun x => (tuples k L).map (x :: ·)

/-- The enumeration of `D_σ`: `D_o = [0, 1]`; `D_{σ→τ}` is the list of all `|D_τ|^{|D_σ|}`
function tables that are monotone (`x ≤ y ⇒ f(x) ≤ f(y)` for all `x, y ∈ D_σ`). -/
def enum : Ty → List SVal
  | .o => [.bit false, .bit true]
  | .arr σ τ =>
      let dσ := enum σ
      ((tuples dσ.length (enum τ)).filter fun l =>
        (List.range dσ.length).all fun i => (List.range dσ.length).all fun j =>
          !(leT σ (dσ.getD i default) (dσ.getD j default)) || leT τ (l.getD i default) (l.getD j default)
      ).map SVal.tab

/-- Application in `D_{σ→τ}`: table lookup at the position of the argument in `D_σ`. -/
def appT (σ : Ty) (f x : SVal) : SVal :=
  match f with
  | .tab l => l.getD ((enum σ).findIdx fun y => leT σ x y && leT σ y x) default
  | .bit _ => default

/-- The least element `⊥_σ`: `0` at ground type, the constant-`⊥_τ` table at `σ → τ`. -/
def botV : Ty → SVal
  | .o => .bit false
  | .arr σ τ => .tab (List.replicate (enum σ).length (botV τ))

/-- The constant-one curried function `λ d₁ ⋯ dᵣ. 1` at `σ₁ → ⋯ → σᵣ → o`. -/
def oneV : Ty → SVal
  | .o => .bit true
  | .arr σ τ => .tab (List.replicate (enum σ).length (oneV τ))

namespace HORS

/-- Term denotation `⟦t⟧_{η,ρ}` (Equation (27)) in the parameter context `ctx`: lookup for
parameters and nonterminals, the constant-one function for a terminal (children are not
evaluated), and table application for `t u`. -/
def den (G : HORS) (ctx : List Ty) (η ρ : List SVal) : Tm → SVal
  | .var i => ρ.getD i default
  | .nt F => η.getD F default
  | .tm c =>
      match G.alphabet[c]? with
      | some r => oneV (termTy r)
      | none => default
  | .app t u =>
      match G.typeOf ctx u with
      | some σ => appT σ (G.den ctx η ρ t) (G.den ctx η ρ u)
      | none => default

/-- The curried table of a rule body: at type `σ → τ`, one entry per `x ∈ D_σ` (in order), with
`x` appended to the local environment; at ground type, the body's denotation. -/
def ruleTab (G : HORS) (ctx : List Ty) (η : List SVal) (body : Tm) : Ty → List SVal → SVal
  | .o, ρ => G.den ctx η ρ body
  | .arr σ τ, ρ => .tab ((enum σ).map fun x => G.ruleTab ctx η body τ (ρ ++ [x]))

/-- One simultaneous update of the global environment, `Φ_G(η)(F)(v⃗) = ⟦t_F⟧_{η, ρ_{v⃗}}`. -/
def Phi (G : HORS) (η : List SVal) : List SVal :=
  (List.range G.nts.length).map fun F =>
    let τ := G.nts.getD F .o
    G.ruleTab τ.args η (G.rules.getD F (.tm 0)) τ []

/-- The all-bottom environment `η₀(F) = ⊥_{τ_F}`. -/
def eta0 (G : HORS) : List SVal := G.nts.map botV

/-- `B = |E_G| = ∏_F |D_{τ_F}|`, the number of global environments. -/
def envCard (G : HORS) : ℕ := (G.nts.map fun τ => (enum τ).length).prod

/-- `η* = η_B = Φ_G^B(η₀)`. -/
def etaStar (G : HORS) : List SVal := G.Phi^[G.envCard] G.eta0

/-- The terminal application exposed after `n` head steps, if any. -/
def exposeAt (G : HORS) (n : ℕ) (t : Tm) : Option (ℕ × List Tm) := exposed (G.run n t)

/-- Unbounded search over increasing head-unfolding budgets for a terminal exposure. -/
def headSearch (G : HORS) (t : Tm) : Part (ℕ × List Tm) :=
  (Nat.rfind fun n => Part.some (G.exposeAt n t).isSome).bind fun n => Part.ofOption (G.exposeAt n t)

/-- The head reader `head_G(t)` of Section 6.4: `⊥` (`none`) when `⟦t⟧_{η*} = 0`; otherwise search
budgets until a terminal application is exposed and return it. -/
def headR (G : HORS) (t : Tm) : Part (Option (ℕ × List Tm)) :=
  match G.den [] G.etaStar [] t with
  | .bit true => (G.headSearch t).map some
  | _ => Part.some none

/-- The exact address reader `read_G(t, w)` of Section 6.4: the label at an existing node, `⊥` at
a present divergent node, `†` (`absent`) otherwise. -/
def read (G : HORS) : Tm → List ℕ → Part Lab
  | t, [] =>
      (G.headR t).map fun
        | none => .bot
        | some (c, _) => .term c
  | t, i :: w =>
      (G.headR t).bind fun
        | none => Part.some .absent
        | some (_, us) => if h : i < us.length then G.read us[i] w else Part.some .absent

/-- The maximum terminal arity `b` (zero for an empty alphabet). -/
def maxArity (G : HORS) : ℕ := G.alphabet.foldr max 0

end HORS

/-- All words over `{0, …, b − 1}` of length strictly less than `d`, in a fixed order. -/
def addrs (b : ℕ) : ℕ → List (List ℕ)
  | 0 => []
  | d + 1 => [] :: (List.range b).flatMap fun i => (addrs b d).map (i :: ·)

namespace HORS

/-- The exact prefix `Pref(G, t, d)`: the label, `⊥` or absence of `BT_G(t)` at every word over
`{0, …, b − 1}` of length `< d`, listed with its address. -/
noncomputable def Pref (G : HORS) (t : Tm) (d : ℕ) : List (List ℕ × Lab) :=
  (addrs G.maxArity d).map fun w => (w, G.BTat t w)

end HORS

end TreeEquivalenceHORS.Equivalence


