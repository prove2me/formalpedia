-- Prove2me | Definitions.Def_gribov_gauge_group
-- name    : gribov_gauge_group
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-13T14:10:45.489814+00:00
-- url     : https://prove2.me/theorems/53e245c3-aece-4d29-93f3-bfe2118d2bef
-- title:
--   Gauge group of the trivial $SU(N)$-bundle over $S^r$
-- statement:
--   The structure group $SU(N)$ of complex $N \times N$ special unitary matrices with its subspace topology (together with the instance making it a topological group), the $r$-sphere $S^r \subset \mathbb{R}^{r+1}$ with north pole as base point, and three groups attached to the trivial $SU(N)$-bundle over a space $M$: the gauge group $\mathcal{G}(M,N) = C(M, SU(N))$ of continuous maps with pointwise multiplication and the compact-open topology; the based gauge group $\mathcal{G}_m = \{\varphi : \varphi(m) = I\}$; and the reduced gauge group $\overline{\mathcal{G}}(M,N) = \mathcal{G}(M,N)/Z_N$, the quotient by the normal subgroup of constant maps with value in the centre of $SU(N)$, with the quotient topology. Gauge transformations are continuous, not smooth, and the bundle is the trivial one.
-- source:
--   I. M. Singer, Some Remarks on the Gribov Ambiguity, Commun. Math. Phys. 60 (1978) 7-12, https://doi.org/10.1007/BF01609471, pp. 7-9, Sect. 1-2 (notation 21, (5), (5)_m, Z_N)

import Mathlib

/-!
# The gauge group of the trivial `SU(N)`-bundle over a sphere

Setting for I. M. Singer, *Some Remarks on the Gribov Ambiguity*,
Commun. Math. Phys. **60** (1978), 7–12.
-/

namespace Gribov

open scoped Topology

/-- The structure group `SU(N)`, realised as the special unitary group of `N × N`
complex matrices with its subspace topology. -/
abbrev SU (N : ℕ) : Type := Matrix.specialUnitaryGroup (Fin N) ℂ

/-- `SU(N)` is a topological group: multiplication is continuous because it is a submonoid
of the matrix algebra, and inversion is continuous because it is the conjugate transpose. -/
instance instIsTopologicalGroupSU (N : ℕ) : IsTopologicalGroup (SU N) where
  continuous_inv := by
    refine continuous_induced_rng.2 ?_
    have h : (Subtype.val ∘ fun A : SU N => A⁻¹)
        = fun A : SU N => star ((A : Matrix (Fin N) (Fin N) ℂ)) := by
      funext A
      exact Matrix.ext fun i => congrFun rfl
    rw [h]
    exact continuous_star.comp continuous_induced_dom

/-- The `r`-dimensional sphere `S^r`, the unit sphere of `ℝ^{r+1}`. -/
abbrev Sphere (r : ℕ) : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin (r + 1))) 1

/-- A base point of `S^r`. -/
noncomputable def northPole (r : ℕ) : Sphere r :=
  ⟨EuclideanSpace.single 0 (1 : ℝ), by simp⟩

/-- The gauge group of the trivial `SU(N)`-bundle over `M`: continuous maps `M → SU(N)` under
pointwise multiplication, with the compact-open topology. -/
abbrev GaugeGroup (M : Type) [TopologicalSpace M] (N : ℕ) : Type := C(M, SU N)

/-- The based gauge group `𝒢_m`: gauge transformations that are the identity at `m`. -/
def BasedGaugeGroup (M : Type) [TopologicalSpace M] (N : ℕ) (m : M) :
    Subgroup (GaugeGroup M N) where
  carrier := {φ | φ m = 1}
  one_mem' := rfl
  mul_mem' := by
    intro a b ha hb
    have ha' : a m = 1 := ha
    have hb' : b m = 1 := hb
    show (a * b) m = 1
    rw [show (a * b) m = a m * b m from rfl, ha', hb', mul_one]
  inv_mem' := by
    intro a ha
    have ha' : a m = 1 := ha
    show a⁻¹ m = 1
    rw [show a⁻¹ m = (a m)⁻¹ from rfl, ha', inv_one]

/-- The subgroup `Z_N ⊆ 𝒢` of gauge transformations that are constant with value in the centre
of `SU(N)`. These act trivially on connections. -/
def CentralConstants (M : Type) [TopologicalSpace M] (N : ℕ) : Subgroup (GaugeGroup M N) where
  carrier := {φ | ∃ c ∈ Subgroup.center (SU N), ∀ x, φ x = c}
  one_mem' := ⟨1, Subgroup.one_mem _, fun _ => rfl⟩
  mul_mem' := by
    rintro a b ⟨c, hc, hac⟩ ⟨d, hd, hbd⟩
    exact ⟨c * d, Subgroup.mul_mem _ hc hd, fun x => by simp [hac x, hbd x]⟩
  inv_mem' := by
    rintro a ⟨c, hc, hac⟩
    exact ⟨c⁻¹, Subgroup.inv_mem _ hc, fun x => by simp [hac x]⟩

instance instNormalCentralConstants (M : Type) [TopologicalSpace M] (N : ℕ) :
    (CentralConstants M N).Normal := by
  constructor
  rintro n ⟨c, hc, hnc⟩ g
  refine ⟨c, hc, fun x => ?_⟩
  have h1 : (g * n * g⁻¹) x = g x * n x * (g x)⁻¹ := rfl
  rw [h1, hnc x]
  have h2 := (Subgroup.mem_center_iff.mp hc) (g x)
  simp [h2, mul_assoc]

/-- The reduced gauge group `𝒢̄ = 𝒢 / Z_N`, with the quotient topology. -/
abbrev ReducedGaugeGroup (M : Type) [TopologicalSpace M] (N : ℕ) : Type :=
  GaugeGroup M N ⧸ CentralConstants M N

end Gribov


