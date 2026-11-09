-- Prove2me | Definitions.Def_MajorityDepthThree_Exact_Restrictions
-- name    : MajorityDepthThree_Exact_Restrictions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:22:37.957024+00:00
-- url     : https://prove2.me/theorems/12081fba-bed9-41fa-a569-e5c80f61a394
-- title:
--   Generalized restrictions, residual families and lifted weights
-- statement:
--   For a finite ground set $V$, a restriction $\rho$ has disjoint positive and negative supports $P,N\subseteq V$, fixes these variables to one and zero respectively, and leaves $V\setminus(P\cup N)$ unset. It may carry additional signed clauses on unset variables as in Note 5.3. A set $S$ is strongly consistent when $P\subseteq S$, $S\cap N=\varnothing$, and its unset projection satisfies the additional clauses. For a family $\mathcal A$ define
--
--   $$\mathcal A_\rho=\{S\setminus P:S\in\mathcal A,\ S\text{ strongly consistent with }\rho\}.$$
--
--   Compatibility requires only $P\subseteq S$ and $S\setminus(P\cup N)\in\mathcal A_\rho$. It permits $S\cap N\ne\varnothing$. The lifted weight $L_\rho(f)(S)$ equals $f(S\setminus P)$ on strongly consistent $S$ and zero otherwise. Scaled combinations sum these lifts pointwise.
--
--   For families over disjoint grounds, the product family consists of pairwise unions and the product weight evaluates the original weights on intersections with their respective grounds. The operation setting a variable $a$ to one retains members containing $a$ and erases $a$. The CNF restriction removes satisfied clauses, deletes fixed literals from the remaining clauses, and adjoins the extra residual clauses. Empty clauses are retained, so inconsistent branches stay unsatisfiable.
--
--   This interface supports both ordinary restrictions and the augmented branches used in Section 5.10. Residual sets keep their original variable names but lie in the smaller ground set; no new free variables are introduced.
-- source:
--   Mohit Gurumukhani, Daniel Kleber, Ramamohan Paturi, Christopher Rosin, Michael Saks, Navid Talebanfard, STOC 2027 submission #677 (October 2026), pp.13–15, Definitions 5.1, 5.4, 5.6, 5.9, Note 5.3, Section 5.2; p.25, Section 5.10

import Definitions.Def_MajorityDepthThree_Exact_Covering

set_option autoImplicit false

namespace MajorityDepthThree.Exact

variable {α : Type} [DecidableEq α]

structure Restriction (V : Finset α) where
  pos : Finset α
  neg : Finset α
  pos_sub : pos ⊆ V
  neg_sub : neg ⊆ V
  disjoint : Disjoint pos neg
  extra : CNF α
  extra_valid : ValidCNF (V \ (pos ∪ neg)) extra

variable {V : Finset α}

def Restriction.support (ρ : Restriction V) : Finset α := ρ.pos ∪ ρ.neg

def StronglyConsistent (ρ : Restriction V) (S : Finset α) : Prop :=
  ρ.pos ⊆ S ∧ Disjoint S ρ.neg ∧ ∀ c ∈ ρ.extra, c.Holds (S \ ρ.support)

noncomputable def residual (A : Family α) (ρ : Restriction V) : Family α := by
  classical
  exact (A.filter (StronglyConsistent ρ)).image (fun S => S \ ρ.pos)

def Compatible (A : Family α) (ρ : Restriction V) (S : Finset α) : Prop :=
  ρ.pos ⊆ S ∧ S \ ρ.support ∈ residual A ρ

noncomputable def liftWeight (ρ : Restriction V) (f : Weight α) : Weight α := by
  classical
  exact fun S => if StronglyConsistent ρ S then f (S \ ρ.pos) else 0

noncomputable def combinedWeight {k : ℕ} (ρ : Fin k → Restriction V)
    (coeff : Fin k → ℝ) (f : Fin k → Weight α) : Weight α :=
  fun S => ∑ i, coeff i * liftWeight (ρ i) (f i) S

noncomputable def productFamily (A B : Family α) : Family α := by
  classical
  exact (A ×ˢ B).image (fun x => x.1 ∪ x.2)

def productWeight (V₁ V₂ : Finset α) (f g : Weight α) : Weight α :=
  fun S => f (S ∩ V₁) * g (S ∩ V₂)

noncomputable def setOne (a : α) (A : Family α) : Family α := by
  classical
  exact (A.filter (fun S => a ∈ S)).image (fun S => S.erase a)

noncomputable def restrictCNF (F : CNF α) (ρ : Restriction V) : CNF α := by
  classical
  exact ((F.filter (fun c => Disjoint c.1 ρ.pos ∧ Disjoint c.2 ρ.neg)).image
    (fun c => (c.1 \ ρ.support, c.2 \ ρ.support))) ∪ ρ.extra

end MajorityDepthThree.Exact


