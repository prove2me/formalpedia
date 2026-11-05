-- Prove2me | Definitions.Def_BundleGerbeStable_CxBundle
-- name    : BundleGerbeStable_CxBundle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:43:08.80052+00:00
-- url     : https://prove2.me/theorems/d049350d-4d5e-4453-bd68-122595a5540e
-- title:
--   Principal $\mathbb C^\times$ bundles over a diffeological space, and the dual bundle
-- statement:
--   A **principal $\mathbb C^\times$ bundle** over a diffeological space $X$ consists of a diffeological total space $P$, a smooth projection $P\to X$, and a smooth action of $\mathbb C^\times$ on $P$ that preserves the fibres and is simply transitive on each fibre, subject to **local triviality**: every $x\in X$ has an open neighbourhood $W$ in the D-topology of $X$ and a $\mathbb C^\times$-equivariant diffeomorphism over $W$
--   $$P|_W \;\cong\; W\times\mathbb C^\times.$$
--
--   The **dual bundle** $Q^*$ is the same space with the action $z\cdot p := z^{-1}p$.
--
--   These are the fibres and coefficients of a bundle gerbe.
--
--   **Formalization Note.** Local triviality is a diffeomorphism in both directions: a mere smooth section would allow $P$ a finer diffeology. It makes the bundle surjective. As $\mathbb C^\times$ is commutative, a left action is the paper's right action.
-- source:
--   Murray, Stevenson, Bundle gerbes: stable isomorphism and local theory, arXiv:math/9908135v1, https://arxiv.org/abs/math/9908135v1, §2, p.2 (principal C× spaces, dual)

import Mathlib
import Definitions.Def_BundleGerbeStable_Diffeologies

open Diffeology

namespace BundleGerbeStable

universe u

/-- A **principal ℂ× bundle** over a diffeological space `X` (Murray, Stevenson, *Bundle gerbes: stable
isomorphism and local theory*, arXiv:math/9908135v1, §2, p.2): a total space `P`, a smooth projection
`proj`, a smooth action of `ℂˣ` that preserves fibres and is simply transitive on each of them, and
local triviality.

**Formalization Note.** Local triviality is stated with an equivariant **diffeomorphism**
`proj⁻¹ W ≃ W × ℂˣ` over `W` (both directions `DSmooth`), for `W` open in the D-topology of `X`. A
mere smooth local section would let `P` carry a finer diffeology. It makes the bundle surjective.
`ℂˣ` is commutative, so the left action written here is the paper's right action `σ g`. -/
structure CxBundle (X : Type u) [DiffeologicalSpace X] where
  /-- The total space. -/
  P : Type u
  /-- The diffeology of the total space. -/
  [diff : DiffeologicalSpace P]
  /-- The action of `ℂˣ` on the total space. -/
  [act : MulAction ℂˣ P]
  /-- The projection to the base. -/
  proj : P → X
  proj_smooth : DSmooth proj
  act_smooth : DSmooth (fun r : ℂˣ × P ↦ r.1 • r.2)
  proj_smul : ∀ (z : ℂˣ) (p : P), proj (z • p) = proj p
  simply_transitive : ∀ p q : P, proj p = proj q → ∃! z : ℂˣ, z • p = q
  locally_trivial : ∀ x : X, ∃ W : Set X, @IsOpen X dTopology W ∧ x ∈ W ∧
    ∃ φ : (proj ⁻¹' W) ≃ (W × ℂˣ), DSmooth φ ∧ DSmooth φ.symm ∧
      (∀ p, (((φ p).1 : W) : X) = proj p.1) ∧
      ∀ (z : ℂˣ) (p q : proj ⁻¹' W), q.1 = z • p.1 → φ q = ((φ p).1, z * (φ p).2)

attribute [instance] CxBundle.diff CxBundle.act

namespace CxBundle

variable {X : Type u} [DiffeologicalSpace X]

/-- The action of `ℂˣ` on the dual: `z` acts as `z⁻¹`. -/
@[instance_reducible]
def dualAct (Q : CxBundle X) : MulAction ℂˣ Q.P where
  smul := fun z p ↦ z⁻¹ • p
  one_smul := fun p ↦ by
    show (1 : ℂˣ)⁻¹ • p = p
    simp
  mul_smul := fun x y p ↦ by
    show (x * y)⁻¹ • p = x⁻¹ • y⁻¹ • p
    rw [mul_inv, mul_smul]

/-- The **dual** bundle `Q*` (arXiv:math/9908135v1, §2, p.2): "this is the same space as R but with the
inverse C× action", fibrewise. -/
def dual (Q : CxBundle X) : CxBundle X :=
  { P := Q.P
    diff := Q.diff
    act := Q.dualAct
    proj := Q.proj
    proj_smooth := Q.proj_smooth
    act_smooth := Q.act_smooth.comp
      (DSmooth.prodMk' (dSmooth_units_inv.comp dSmooth_fst) dSmooth_snd)
    proj_smul := fun z p ↦ Q.proj_smul z⁻¹ p
    simply_transitive := fun p q h ↦ by
      obtain ⟨z, hz, huniq⟩ := Q.simply_transitive p q h
      refine ⟨z⁻¹, ?_, fun w hw ↦ ?_⟩
      · show (z⁻¹)⁻¹ • p = q
        simpa using hz
      · have hw' : w⁻¹ • p = q := hw
        have := huniq _ hw'
        rw [← this, inv_inv]
    locally_trivial := fun x ↦ by
      obtain ⟨W, hW, hxW, φ, hφ, hφs, hproj, heq⟩ := Q.locally_trivial x
      refine ⟨W, hW, hxW, φ.trans (Equiv.prodCongr (Equiv.refl _) (Equiv.inv ℂˣ)), ?_, ?_, ?_, ?_⟩
      · exact (DSmooth.prodMk' dSmooth_fst (dSmooth_units_inv.comp dSmooth_snd)).comp hφ
      · exact hφs.comp (DSmooth.prodMk' dSmooth_fst (dSmooth_units_inv.comp dSmooth_snd))
      · exact hproj
      · intro z p q hq
        have hq' : q.1 = z⁻¹ • p.1 := hq
        have := heq z⁻¹ p q hq'
        simp [this, mul_comm] }

end CxBundle

end BundleGerbeStable


