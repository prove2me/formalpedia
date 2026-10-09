-- Prove2me | Definitions.Def_MPSTAsync_Progress_Projection
-- name    : MPSTAsync_Progress_Projection
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T23:07:07.396732+00:00
-- url     : https://prove2.me/theorems/7ca341e6-a184-498a-9aba-78a62dd18c93
-- title:
--   Defs. 4.1–4.2 and 5.8 — partial projection and coherence
-- statement:
--   The **projection** $G\upharpoonright p$ extracts role $p$'s endpoint type from a global conversation. It is undefined when a third party sees incompatible alternatives or when parallel components share a participant. A global type is **coherent** when it is well formed and linear, projects for every participant, and its carried global types meet the same conditions. A family of located endpoint types is coherent when it agrees with the projections of one coherent global type.
--
--   $$\llbracket G\rrbracket=\{(G\upharpoonright p)@p:p\in\operatorname{pid}(G)\}.$$
--
--   Full projection supplies the target families for runtime typing.
--
--   **Formalization Note** Projection is an `Option` valued syntactic map. Endpoint equality is witnessed by a bisimulation of regular trees, so unfolding a recursive type does not change its meaning.
-- source:
--   Honda, Yoshida, Carbone, Multiparty Asynchronous Session Types, J. ACM 63(1) (2016), Art. 9, pp. 22–23, 31, Defs. 4.1–4.2 and 5.8, https://doi.org/10.1145/2827695

import Definitions.Def_MPSTAsync_Progress_Linearity

set_option autoImplicit false

namespace MPSTAsync.Progress

-- Definition 4.1: syntactic partial projection.  A third party must see
-- exactly the same syntax in every branch.
noncomputable def projFuel : ℕ → GType → Role → Option EType
  | 0, _, _ => none
  | n+1, .comm p q k U G, r => do
      let T ← projFuel n G r
      if r = p then some (.send k U T)
      else if r = q then some (.recv k U T)
      else some T
  | n+1, .branch p q k bs, r => do
      let projected ← bs.mapM (fun x => do
        let T ← projFuel n x.2 r
        pure (x.1,T))
      if r = p then some (.sel k projected)
      else if r = q then some (.bra k projected)
      else match projected with
        | [] => some .stop
        | (_,T)::rest => if rest.all (fun x => x.2 == T) then some T else none
  | n+1, .par G H, r =>
      if r ∈ G.pid then
        if r ∈ H.pid then none else projFuel n G r
      else if r ∈ H.pid then projFuel n H r else some .stop
  | n+1, .mu t G, r => do
      let T ← projFuel n G r
      if T == .stop then some .stop else some (.mu t T)
  | _+1, .var t, _ => some (.var t)
  | _+1, .stop, _ => some .stop

noncomputable def proj (G : GType) (r : Role) : Option EType :=
  projFuel (sizeOf G) G r

-- End-point substitution differs from substitution in carried global types.
def EType.substEFuel : ℕ → TVar → EType → EType → EType
  | 0, _, _, T => T
  | n+1, t, R, .send k U T => .send k U (T.substEFuel n t R)
  | n+1, t, R, .recv k U T => .recv k U (T.substEFuel n t R)
  | n+1, t, R, .sel k bs => .sel k (bs.map fun x => (x.1,x.2.substEFuel n t R))
  | n+1, t, R, .bra k bs => .bra k (bs.map fun x => (x.1,x.2.substEFuel n t R))
  | n+1, t, R, .mu u T => if u = t then .mu u T else .mu u (T.substEFuel n t R)
  | _+1, t, R, .var u => if u = t then R else .var u
  | _+1, _, _, .stop => .stop

noncomputable def EType.substE (T : EType) (t : TVar) (R : EType) : EType :=
  T.substEFuel (sizeOf T) t R

noncomputable def EType.unfoldHead : EType → EType
  | .mu t T => T.substE t (.mu t T)
  | T => T

-- Equality of regular trees is witnessed by a post-fixed bisimulation.
def sameBranches (R : Set (EType × EType))
    (bs cs : List (Label × EType)) : Prop :=
  (bs.map Prod.fst).toFinset = (cs.map Prod.fst).toFinset ∧
  (bs.map Prod.fst).Nodup ∧ (cs.map Prod.fst).Nodup ∧
  ∀ x ∈ bs, ∀ y ∈ cs, x.1 = y.1 → (x.2,y.2) ∈ R

def BisimStep (R : Set (EType × EType)) (T U : EType) : Prop :=
  match T, U with
  | .mu t A, B => (A.substE t (.mu t A), B) ∈ R
  | A, .mu t B => (A, B.substE t (.mu t B)) ∈ R
  | .send k V A, .send j W B => k = j ∧ V = W ∧ (A,B) ∈ R
  | .recv k V A, .recv j W B => k = j ∧ V = W ∧ (A,B) ∈ R
  | .sel k as, .sel j bs => k = j ∧ sameBranches R as bs
  | .bra k as, .bra j bs => k = j ∧ sameBranches R as bs
  | .var t, .var u => t = u
  | .stop, .stop => True
  | _, _ => False

def EEquiv (T U : EType) : Prop :=
  ∃ R : Set (EType × EType), (T,U) ∈ R ∧
    ∀ A B, (A,B) ∈ R → BisimStep R A B

-- Sid of an end-point type includes indices in its visible prefixes.
def EType.sidFuel : ℕ → EType → Finset ℕ
  | 0, _ => ∅
  | n+1, .send k _ T | n+1, .recv k _ T => insert k (T.sidFuel n)
  | n+1, .sel k bs | n+1, .bra k bs =>
      insert k (bs.foldl (fun s x => s ∪ x.2.sidFuel n) ∅)
  | n+1, .mu _ T => T.sidFuel n
  | _+1, .var _ | _+1, .stop => ∅

noncomputable def EType.sid (T : EType) : Finset ℕ := T.sidFuel (sizeOf T)

def Coherent (G : GType) : Prop :=
  G.WellFormed ∧ IsLinear G ∧
  (∀ p ∈ G.pid, ∃ T, proj G p = some T) ∧
  (∀ H ∈ G.allCarried, H.WellFormed ∧ IsLinear H ∧
    ∀ p ∈ H.pid, ∃ T, proj H p = some T)

abbrev Family := List (EType × Role)

def Family.roles (F : Family) : Finset Role := (F.map Prod.snd).toFinset

def Family.WellFormed (F : Family) : Prop :=
  (F.map Prod.snd).Nodup ∧ ∀ x ∈ F, x.1.WellFormed

def FamilyCoherent (F : Family) : Prop :=
  F.WellFormed ∧ ∃ G, Coherent G ∧ F.roles = G.pid ∧
    ∀ x ∈ F, ∃ T, proj G x.2 = some T ∧ EEquiv x.1 T

noncomputable def fullProj (G : GType) : Option Family :=
  by classical
     exact if Coherent G then
       G.pid.toList.mapM (fun p => (proj G p).map fun T => (T,p))
     else none

end MPSTAsync.Progress


