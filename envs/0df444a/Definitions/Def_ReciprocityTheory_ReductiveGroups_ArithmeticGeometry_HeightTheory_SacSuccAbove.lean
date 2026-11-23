-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SacSuccAbove
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SacSuccAbove
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:35:04.009076+00:00
-- url     : https://prove2.me/theorems/ec377c71-8588-412f-8d97-b48c6dc7e64e
-- title:
--   Sac Succ Above
-- statement:
--   Definitions and structural lemmas for Sac Succ Above, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SacSuccAbove.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial
noncomputable def tauPev {K : Type} [Field K] {D N : ℕ} (sg : K →+* ℂ) (pt : TVar D N → ℂ)
    (hpt : ∀ q : MvPolynomial (TVar D N) K, q ≠ 0 → eval₂ sg pt q ≠ 0) : KTf K D N →+* ℂ :=
  IsFractionRing.lift (A := KTp K D N) (g := eval₂Hom sg pt)
    ((injective_iff_map_eq_zero _).2 fun q hq => by_contra fun h0 => hpt q h0 hq)
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
namespace Data
variable (d : Data K ι Ω WT A)
noncomputable def pImg (c : ι) (p : TVar d.D d.N) : MvPolynomial (SVar d.D d.N) (Ω c) :=
  Fin.succAboveCases (α := fun _ => MvPolynomial (SVar d.D d.N) (Ω c)) (d.jc c)
    (if p.1 = 0 then X (Sum.inl ())
      else -∑ k, X (Sum.inr (p.1, k)) * C (d.x c k))
    (fun k => X (Sum.inr (p.1, k))) p.2
noncomputable def sHp (c : ι) : MvPolynomial (TVar d.D d.N) K →ₐ[K] MvPolynomial (SVar d.D d.N) (Ω c) :=
  aeval (d.pImg c)
noncomputable def evP (c : ι) (P : Ω c →+* ℂ) (pt : TVar d.D d.N → ℂ) :
    MvPolynomial (SVar d.D d.N) (Ω c) →+* ℂ :=
  eval₂Hom P (Sum.elim (fun _ => pt (0, d.jc c)) (fun ik => pt (ik.1, (d.jc c).succAbove ik.2)))
section emb
variable (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (sg : K →+* ℂ) (pt : TVar d.D d.N → ℂ)
  (hpt : ∀ q : MvPolynomial (TVar d.D d.N) K, q ≠ 0 → eval₂ sg pt q ≠ 0)
end emb
end Data
end ReciprocityTheory.ChartRestriction.G.T0


