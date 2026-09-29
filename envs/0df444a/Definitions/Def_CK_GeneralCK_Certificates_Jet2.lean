-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Jet2
-- name    : CK_GeneralCK_Certificates_Jet2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:16:07.214759+00:00
-- url     : https://prove2.me/theorems/5e90bcab-53be-4a0e-97b6-8dab7fcdbcb2
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Jet2` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Jet2` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Jet2` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Jet2 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Jet2.lean)

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_GeneralCK_RB2_checker_semantics_v2
import Definitions.Def_GeneralCK_RB2_program_data

namespace GeneralCK.Certificates







namespace Jet2
open scoped Topology


































theorem soundAt_const (c t : ℝ) : (const c).SoundAt t :=
  ⟨hasDerivAt_const t c, hasDerivAt_const t 0⟩

theorem soundAt_variable (t : ℝ) : variableJet.SoundAt t :=
  ⟨hasDerivAt_id t, hasDerivAt_const t 1⟩

theorem SoundAt.add {j k : Jet2} {t : ℝ} (hj : j.SoundAt t) (hk : k.SoundAt t) :
    (j.add k).SoundAt t := ⟨hj.1.add hk.1, hj.2.add hk.2⟩

theorem SoundAt.neg {j : Jet2} {t : ℝ} (hj : j.SoundAt t) :
    j.neg.SoundAt t := ⟨hj.1.neg, hj.2.neg⟩

theorem SoundAt.mul {j k : Jet2} {t : ℝ} (hj : j.SoundAt t) (hk : k.SoundAt t) :
    (j.mul k).SoundAt t := by
  refine ⟨hj.1.mul hk.1, ?_⟩
  have hh := (hj.2.mul hk.1).add (hj.1.mul hk.2)
  convert! hh using 1
  simp only [Jet2.mul]
  ring

theorem SoundAt.inv {j : Jet2} {t : ℝ} (hj : j.SoundAt t) (hn : j.value t ≠ 0) :
    j.inv.SoundAt t := by
  constructor
  · convert! hj.1.inv hn using 1
  · have hh := hj.2.neg.div (hj.1.pow 2) (pow_ne_zero 2 hn)
    convert! hh using 1
    simp only [Jet2.inv, Pi.pow_apply, Pi.neg_apply]
    field_simp [hn]
    ring

theorem SoundAt.log {j : Jet2} {t : ℝ} (hj : j.SoundAt t) (hn : j.value t ≠ 0) :
    j.log.SoundAt t := by
  refine ⟨hj.1.log hn, ?_⟩
  have hh := hj.2.div hj.1 hn
  convert! hh using 1
  simp only [Jet2.log]
  field_simp [hn]

theorem soundOn_const (c : ℝ) (s : Set ℝ) : (const c).SoundOn s :=
  fun t _ => soundAt_const c t

theorem soundOn_variable (s : Set ℝ) : variableJet.SoundOn s :=
  fun t _ => soundAt_variable t

theorem SoundOn.add {j k : Jet2} {s : Set ℝ} (hj : j.SoundOn s) (hk : k.SoundOn s) :
    (j.add k).SoundOn s := fun t ht => (hj t ht).add (hk t ht)

theorem SoundOn.neg {j : Jet2} {s : Set ℝ} (hj : j.SoundOn s) :
    j.neg.SoundOn s := fun t ht => (hj t ht).neg

theorem SoundOn.mul {j k : Jet2} {s : Set ℝ} (hj : j.SoundOn s) (hk : k.SoundOn s) :
    (j.mul k).SoundOn s := fun t ht => (hj t ht).mul (hk t ht)

theorem SoundOn.inv {j : Jet2} {s : Set ℝ} (hj : j.SoundOn s)
    (hn : ∀ t ∈ s, j.value t ≠ 0) : j.inv.SoundOn s :=
  fun t ht => (hj t ht).inv (hn t ht)

theorem SoundOn.log {j : Jet2} {s : Set ℝ} (hj : j.SoundOn s)
    (hn : ∀ t ∈ s, j.value t ≠ 0) : j.log.SoundOn s :=
  fun t ht => (hj t ht).log (hn t ht)

theorem SoundOn.mono {j : Jet2} {s u : Set ℝ} (hj : j.SoundOn s) (hu : u ⊆ s) :
    j.SoundOn u := fun t ht => hj t (hu ht)

/-- A locally sound jet supplies a derivative of the actual first derivative.
The neighborhood assumption prevents identifying a second derivative from
an isolated pointwise assertion about an arbitrarily chosen first function. -/
theorem SoundOn.hasDerivAt_deriv {j : Jet2} {s : Set ℝ} {t : ℝ}
    (hj : j.SoundOn s) (hs : s ∈ 𝓝 t) :
    HasDerivAt (deriv j.value) (j.second t) t := by
  have ht : t ∈ s := mem_of_mem_nhds hs
  apply (hj t ht).2.congr_of_eventuallyEq
  filter_upwards [hs] with u hu
  exact (hj u hu).1.deriv

theorem SoundOn.deriv_deriv {j : Jet2} {s : Set ℝ} {t : ℝ}
    (hj : j.SoundOn s) (hs : s ∈ 𝓝 t) :
    deriv (deriv j.value) t = j.second t := (hj.hasDerivAt_deriv hs).deriv

end Jet2
end GeneralCK.Certificates


