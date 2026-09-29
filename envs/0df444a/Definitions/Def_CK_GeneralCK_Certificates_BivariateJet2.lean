-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_BivariateJet2
-- name    : CK_GeneralCK_Certificates_BivariateJet2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:23:54.292522+00:00
-- url     : https://prove2.me/theorems/70925d6c-6765-4271-8f18-f73d762d9183
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.BivariateJet2` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.BivariateJet2` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.BivariateJet2` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.BivariateJet2 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/BivariateJet2.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Jet2Composition
import Definitions.Def_CK_GeneralCK_Certificates_ReflectionTaylor
import Definitions.Def_GeneralCK_RB2_checker_semantics_v2
import Definitions.Def_GeneralCK_RB2_program_data

namespace GeneralCK.Certificates












namespace BivariateJet2



























































private theorem jet_ext {j k : Jet2} (hv : j.value=k.value)
    (hf : j.first=k.first) (hs : j.second=k.second) : j=k := by
  cases j; cases k; simp_all

private theorem biv_ext {j k : BivariateJet2} (hv : j.value=k.value)
    (ha : j.firstA=k.firstA) (hz : j.firstZ=k.firstZ)
    (haa : j.secondAA=k.secondAA) (haz : j.secondAZ=k.secondAZ)
    (hzz : j.secondZZ=k.secondZZ) : j=k := by
  cases j; cases k; simp_all

theorem inv_eq_outerCompose (j : BivariateJet2) :
    j.inv=outerCompose Jet2.variableJet.inv j := by
  apply biv_ext <;> funext t <;>
    simp only [inv,outerCompose,Jet2.inv,Jet2.variableJet,id_eq,div_eq_mul_inv] <;> ring

theorem log_eq_outerCompose (j : BivariateJet2) :
    j.log=outerCompose Jet2.variableJet.log j := by
  apply biv_ext <;> funext t <;>
    simp only [log,outerCompose,Jet2.log,Jet2.variableJet,id_eq,div_eq_mul_inv] <;> ring

@[simp] theorem projection_const (c da dz : ℝ) :
    (const c).projection da dz=Jet2.const c := by
  apply jet_ext <;> funext t <;> simp [projection,const,Jet2.const]

@[simp] theorem projection_affineA (c x dz : ℝ) :
    (affineA c x).projection (x-c) dz=Jet2.segment c x := by
  apply jet_ext <;> funext t <;> simp [projection,affineA,coordinateA,Jet2.segment]

@[simp] theorem projection_affineZ (c x da : ℝ) :
    (affineZ c x).projection da (x-c)=Jet2.segment c x := by
  apply jet_ext <;> funext t <;> simp [projection,affineZ,coordinateZ,Jet2.segment]

@[simp] theorem projection_add (j k : BivariateJet2) (da dz : ℝ) :
    (j.add k).projection da dz=(j.projection da dz).add (k.projection da dz) := by
  apply jet_ext <;> funext t <;> simp only [projection,add,Jet2.add] <;> ring

@[simp] theorem projection_neg (j : BivariateJet2) (da dz : ℝ) :
    j.neg.projection da dz=(j.projection da dz).neg := by
  apply jet_ext <;> funext t <;> simp only [projection,neg,Jet2.neg] <;> ring

@[simp] theorem projection_mul (j k : BivariateJet2) (da dz : ℝ) :
    (j.mul k).projection da dz=(j.projection da dz).mul (k.projection da dz) := by
  apply jet_ext <;> funext t <;> simp only [projection,mul,Jet2.mul] <;> ring

/-- Algebraic commutation is unconditional, including the totalized zero inverse.
Actual derivative soundness still requires the usual nonzero hypothesis. -/
@[simp] theorem projection_inv (j : BivariateJet2) (da dz : ℝ) :
    j.inv.projection da dz=(j.projection da dz).inv := by
  apply jet_ext <;> funext t <;> simp only [projection,inv,Jet2.inv,div_eq_mul_inv] <;> ring

@[simp] theorem projection_log (j : BivariateJet2) (da dz : ℝ) :
    j.log.projection da dz=(j.projection da dz).log := by
  apply jet_ext <;> funext t <;> simp only [projection,log,Jet2.log,div_eq_mul_inv] <;> ring

@[simp] theorem projection_outerCompose (outer : Jet2) (j : BivariateJet2) (da dz : ℝ) :
    (outerCompose outer j).projection da dz=outer.comp (j.projection da dz) := by
  apply jet_ext <;> funext t <;> simp only [projection,outerCompose,Jet2.comp] <;> ring







theorem DirectionalSoundAt.add {j k : BivariateJet2} {da dz t : ℝ}
    (hj : j.DirectionalSoundAt da dz t) (hk : k.DirectionalSoundAt da dz t) :
    (j.add k).DirectionalSoundAt da dz t := by
  simpa only [DirectionalSoundAt,projection_add] using Jet2.SoundAt.add hj hk

theorem DirectionalSoundAt.neg {j : BivariateJet2} {da dz t : ℝ}
    (hj : j.DirectionalSoundAt da dz t) : j.neg.DirectionalSoundAt da dz t := by
  simpa only [DirectionalSoundAt,projection_neg] using Jet2.SoundAt.neg hj

theorem DirectionalSoundAt.mul {j k : BivariateJet2} {da dz t : ℝ}
    (hj : j.DirectionalSoundAt da dz t) (hk : k.DirectionalSoundAt da dz t) :
    (j.mul k).DirectionalSoundAt da dz t := by
  simpa only [DirectionalSoundAt,projection_mul] using Jet2.SoundAt.mul hj hk

theorem DirectionalSoundAt.inv {j : BivariateJet2} {da dz t : ℝ}
    (hj : j.DirectionalSoundAt da dz t) (hn : j.value t≠0) :
    j.inv.DirectionalSoundAt da dz t := by
  simpa only [DirectionalSoundAt,projection_inv] using Jet2.SoundAt.inv hj hn

theorem DirectionalSoundAt.log {j : BivariateJet2} {da dz t : ℝ}
    (hj : j.DirectionalSoundAt da dz t) (hn : j.value t≠0) :
    j.log.DirectionalSoundAt da dz t := by
  simpa only [DirectionalSoundAt,projection_log] using Jet2.SoundAt.log hj hn

theorem DirectionalSoundAt.outerCompose {outer : Jet2} {j : BivariateJet2} {da dz t : ℝ}
    (ho : outer.SoundAt (j.value t)) (hj : j.DirectionalSoundAt da dz t) :
    (outerCompose outer j).DirectionalSoundAt da dz t := by
  simpa only [DirectionalSoundAt,projection_outerCompose] using ho.comp hj

theorem DirectionalSoundOn.outerCompose {outer : Jet2} {j : BivariateJet2}
    {da dz : ℝ} {s u : Set ℝ} (ho : outer.SoundOn u)
    (hj : j.DirectionalSoundOn da dz s) (hm : Set.MapsTo j.value s u) :
    (outerCompose outer j).DirectionalSoundOn da dz s := by
  simpa only [DirectionalSoundOn,projection_outerCompose] using ho.comp hj hm

theorem soundOn_affineA (c x dz : ℝ) (s : Set ℝ) :
    (affineA c x).DirectionalSoundOn (x-c) dz s := by
  simpa only [DirectionalSoundOn,projection_affineA] using Jet2.soundOn_segment c x s

theorem soundOn_affineZ (c x da : ℝ) (s : Set ℝ) :
    (affineZ c x).DirectionalSoundOn da (x-c) s := by
  simpa only [DirectionalSoundOn,projection_affineZ] using Jet2.soundOn_segment c x s

end BivariateJet2
end GeneralCK.Certificates


