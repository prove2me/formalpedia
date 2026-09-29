-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionSmallBiasContactTable
-- name    : CK_GeneralCK_ReflectionSmallBiasContactTable
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T18:12:59.989824+00:00
-- url     : https://prove2.me/theorems/34380128-32e9-4e65-bbc4-7c030eb10d51
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionSmallBiasContactTable` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionSmallBiasContactTable` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionSmallBiasContactTable` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionSmallBiasContactTable

import Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasPicardReplay1
import Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasPicardReplay2
import Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasPicardReplay3
import Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasPicardReplay4
import Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasPicardReplay5
import Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasPicardReplay6
import Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasPicardReplay7
import Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasPicardReplay8
import Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasPicardReplay9
import Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasPicardReplay10
import Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasPicardReplay11
import Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasPicardReplay12
import Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasPicardReplay13
import Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasPicardPhiReplay
import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasContactValueJet

-- ===== source module GeneralCK.ReflectionSmallBiasContactTable =====
section

namespace GeneralCK.Reflection.SmallBiasPicardData

open SmallBiasJet SmallBiasPicard

theorem iterate12_approximates {k : ℂ} (hk : k ≠ 0) (hklog : k = (Real.log 2:ℂ)) :
    Approximates 24 k (fun z => iterate 12 z.1) stage12 := by
  have h0 : Approximates 24 k (fun z => iterate 0 z.1) stage0 := by
    convert Approximates.exactPolynomial 24 k ([] : List SmallBiasPolynomial.Term) using 1
    <;> rfl
  have h1 : Approximates 24 k (fun z => iterate 1 z.1) stage1 :=
    stage1_replay hk hklog h0 (by simp)
  have h2 : Approximates 24 k (fun z => iterate 2 z.1) stage2 :=
    stage2_replay hk hklog h1 (by simp)
  have h3 : Approximates 24 k (fun z => iterate 3 z.1) stage3 :=
    stage3_replay hk hklog h2 (by simp)
  have h4 : Approximates 24 k (fun z => iterate 4 z.1) stage4 :=
    stage4_replay hk hklog h3 (by simp)
  have h5 : Approximates 24 k (fun z => iterate 5 z.1) stage5 :=
    stage5_replay hk hklog h4 (by simp)
  have h6 : Approximates 24 k (fun z => iterate 6 z.1) stage6 :=
    stage6_replay hk hklog h5 (by simp)
  have h7 : Approximates 24 k (fun z => iterate 7 z.1) stage7 :=
    stage7_replay hk hklog h6 (by simp)
  have h8 : Approximates 24 k (fun z => iterate 8 z.1) stage8 :=
    stage8_replay hk hklog h7 (by simp)
  have h9 : Approximates 24 k (fun z => iterate 9 z.1) stage9 :=
    stage9_replay hk hklog h8 (by simp)
  have h10 : Approximates 24 k (fun z => iterate 10 z.1) stage10 :=
    stage10_replay hk hklog h9 (by simp)
  have h11 : Approximates 24 k (fun z => iterate 11 z.1) stage11 :=
    stage11_replay hk hklog h10 (by simp)
  have h12 : Approximates 24 k (fun z => iterate 12 z.1) stage12 :=
    stage12_replay hk hklog h11 (by simp)
  exact h12

theorem iterate_stable_approximates {k : ℂ} (hk : k ≠ 0) (hklog : k = (Real.log 2:ℂ)) (m : ℕ) :
    Approximates 24 k (fun z => iterate (12+m) z.1) stage12 := by
  induction m with
  | zero => exact iterate12_approximates hk hklog
  | succ m ih =>
    exact stage13_replay hk hklog ih (by simp)

theorem phi_approximates_table {k : ℂ} (hk : k ≠ 0) (hklog : k = (Real.log 2:ℂ)) :
    Approximates 24 k (fun z => SmallBiasContactValueJet.phi z.1) phi := by
  apply SmallBiasContactValueJet.phi_from_finite_jet
  exact phi_replay hk (iterate_stable_approximates hk hklog 10) (by simp)

end GeneralCK.Reflection.SmallBiasPicardData

end


