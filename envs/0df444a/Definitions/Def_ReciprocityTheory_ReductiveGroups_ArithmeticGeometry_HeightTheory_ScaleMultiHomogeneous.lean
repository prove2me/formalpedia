-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ScaleMultiHomogeneous
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ScaleMultiHomogeneous
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:36.300743+00:00
-- url     : https://prove2.me/theorems/9c859693-1ee9-4cb3-ab82-f08ce216a5c7
-- title:
--   Scale Multi Homogeneous
-- statement:
--   Definitions and structural lemmas for Scale Multi Homogeneous, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ScaleMultiHomogeneous.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial
section Scale
variable {S σ : Type*} [CommRing S]
noncomputable def scaleEquiv (P : σ → Prop) [DecidablePred P] (u : Sˣ) :
    MvPolynomial σ S ≃ₐ[S] MvPolynomial σ S :=
  AlgEquiv.ofAlgHom (aeval fun v => if P v then C (u : S) * X v else X v)
    (aeval fun v => if P v then C (↑u⁻¹ : S) * X v else X v)
    (by
      ext v
      by_cases hv : P v
      · simp [hv, ← mul_assoc, ← C_mul]
      · simp [hv])
    (by
      ext v
      by_cases hv : P v
      · simp [hv, ← mul_assoc, ← C_mul]
      · simp [hv])
end Scale
section Blocks
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}
def InBlock (b : Fin (D + 1)) (v : SVar D N) : Prop :=
  Sum.elim (fun _ => False) (fun w : Fin (D + 1) × Fin N => w.1 = b) v
instance (b : Fin (D + 1)) : DecidablePred (InBlock (D := D) (N := N) b) := by
  intro v
  cases v <;> simp only [InBlock, Sum.elim_inl, Sum.elim_inr] <;> infer_instance
end Blocks
section Norm
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}
noncomputable def sigP (b : Fin (D + 1)) (u : Kˣ) :
    MvPolynomial (TVar D N) K ≃ₐ[K] MvPolynomial (TVar D N) K :=
  scaleEquiv (fun v : TVar D N => v.1 = b) u
noncomputable def tauP (b : Fin (D + 1)) (u : Kˣ) :
    MvPolynomial (SVar D N) Ω ≃ₐ[Ω] MvPolynomial (SVar D N) Ω :=
  scaleEquiv (InBlock b) (Units.map (algebraMap K Ω).toMonoidHom u)
noncomputable def sigF (b : Fin (D + 1)) (u : Kˣ) : KTf K D N ≃+* KTf K D N :=
  IsFractionRing.ringEquivOfRingEquiv (sigP (N := N) b u).toRingEquiv
noncomputable def tauF (b : Fin (D + 1)) (u : Kˣ) : OmS Ω D N ≃+* OmS Ω D N :=
  IsFractionRing.ringEquivOfRingEquiv (tauP (Ω := Ω) (D := D) (N := N) b u).toRingEquiv
end Norm
namespace Data
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (NumberField.RingOfIntegers K) (A c)]
variable (d : Data K ι Ω WT A)
end Data
end ReciprocityTheory.ChartRestriction.G.T0


