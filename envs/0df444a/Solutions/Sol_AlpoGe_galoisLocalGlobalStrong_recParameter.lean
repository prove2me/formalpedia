-- Prove2me | solution 1 for AlpoGe.galoisLocalGlobalStrong_recParameter
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @RSoulat
-- created : 2026-11-22T18:15:59.410279+00:00
-- url     : https://prove2.me/submissions/6f348df9-c8fc-4082-bc96-d0444114c575
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AlpoGeB008
import Theorems.Thm_AlpoGe_galoisLocalGlobal_geometry_witnesses

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual
open GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
open UpperTheory.GalStar UpperTheory.GalS

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem localCompletionIsQp {E : Type} [Field E] [NumberField E]
    {w : HeightOneSpectrum (𝓞 E)} {n : ℕ} (h : IsQpBig w n) :
    ∃ (p : ℕ) (_ : Fact p.Prime) (iso : ℚ_[p] ≃+* w.adicCompletion E), Continuous iso := by
  obtain ⟨p, hp, iso, hContinuous, _⟩ := h
  exact ⟨p, hp, iso, hContinuous⟩

private theorem restrictAway {E Ω : Type} [Field E] [NumberField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω}
    {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {x y : WD h}
    (compat : x.lpDim = y.lpDim ∧ (Tor y → y.mono0 → x = y) ∧
      ((∃ (p : ℕ) (_ : Fact p.Prime) (iso : ℚ_[p] ≃+* w.adicCompletion E), Continuous iso) →
        TmW y → Sqf y → y.mono0 →
        x.mono0 ∧ ∀ g : ↥(Weil h), deg g = 0 → x.charPol g = y.charPol g)) : AwayB x y where
  dim := compat.1
  tor := compat.2.1
  tame0 hp := compat.2.2 (localCompletionIsQp hp)

theorem solution :
    UpperTheory.GalStar.Row0b fun h rc => UpperTheory.Zero.LLC.IsRecT h rc := by
  intro E Ω _ _ _ _ _ _ l _ ι a ha π χ hRegular hPolarized
  obtain ⟨r, wt, HT, hCont, hSS, hAway, hWeights, hConj, hAbove⟩ :=
    AlpoGe.galoisLocalGlobal_geometry_witnesses E Ω l ι a ha π χ hRegular hPolarized
  refine ⟨r, wt, HT, ?_⟩
  refine
    { cont := hCont
      ss := hSS
      away := ?_
      weights := hWeights
      weights_conj := hConj
      above := ?_ }
  · intro w hl A h rc hRec σ hComponent
    exact restrictAway (hAway w hl A h rc hRec σ hComponent)
  · intro P AI hTied w A h O _ _ _ Bw hj
    obtain ⟨hCrys, hNice⟩ := hAbove P AI hTied w A h O Bw hj
    refine ⟨hCrys, ?_⟩
    intro σ hComponent rc hRec hLocal hMono
    obtain ⟨hDR, hPst, hJumps, hComp⟩ := hNice σ hComponent rc hRec
      (hLocal.imp (fun h => ⟨localCompletionIsQp h.1, h.2⟩) id) hMono
    exact ⟨hDR, hPst, hJumps, restrictAway hComp⟩
