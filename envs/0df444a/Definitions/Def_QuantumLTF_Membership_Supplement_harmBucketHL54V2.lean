-- Prove2me | Definitions.Def_QuantumLTF_Membership_Supplement_harmBucketHL54V2
-- name    : QuantumLTF_Membership_Supplement_harmBucketHL54V2
-- status  : Definition
-- author  : @Robin Kothari
-- created : 2026-11-25T03:42:41.651988+00:00
-- url     : https://prove2.me/theorems/128c0364-5634-42b6-90e5-607b215ae7ed
-- title:
--   Harmonic-Bucket stabilizer state-preparation circuit interface ($\mathrm{HarmBucketHL54V2}$)
-- statement:
--   Defines the `gates12` (`LayeredCircuit`) circuit interface `HarmBucketHL54V2` for controlled preparation of the uniform stabilizer-subgroup superposition
--
--   $$
--   |l\rangle |0\rangle \longmapsto |l\rangle \otimes \frac{1}{\sqrt{|H_l|}} \sum_{h \in H_l} \bigl|\mathrm{padPerm}_{2K, M}(h)(0\dots M-1)\bigr\rangle
--   $$
--
--   for any monotone non-strictly increasing list $l \in \{0, \dots, n-1, \bot\}^{2K}$ and $M = 2^d \ge 2K$ ($d \ge 1$, $s = \lceil \log_2 n \rceil + 1$).
--
--   The size bound scales as $O\bigl((K s + M)\, (L + d)^{K_{\mathrm{hl}}}\bigr)$ with $L = \lceil \log_2((K+1)(n+1)+2) \rceil + 1$, accounting for the $O(M (d+1)^4)$ gate cost of the final in-place Alonso–Schott conversion across all admissible register widths $d$.
--
--   **Formalization Note** Supersedes `HarmBucketHL54` (whose gate-count bound omitted the `d` dependence in `(L + d) ^ K_hl`) and is proved inhabited by `QuantumLTF.Membership.Supplement.harm_bucket_hl_54_v2`.
-- source:
--   Liu, Childs, Gottesman [LCG26], First and second quantization: reversible and quantum circuits (arXiv:2411.04019, Section IV.B–C); Krivcenko, Nguyen, de Wolf [KNW26] (arXiv:2609.40331, Theorem 5.4).

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54Comb
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54Circs

set_option autoImplicit false

/-!
# Corrected Harmonic-Bucket Stabilizer Interface (`HarmBucketHL54V2`)

Corrects the `d`-dependence in `HarmBucketHL54.harmBucketH_lCircuit_size` by replacing
`(L : ℝ) ^ K_hl` with `((L + d : ℕ) : ℝ) ^ K_hl` (where `L = Nat.clog 2 ((K + 1) * (n + 1) + 2) + 1`),
accounting for the `O(arity d * (d + 1)^4)` gate cost of `AlonsoSchottSil54.alonsoSchottCircuit`
across all `1 ≤ d` with `2 * K ≤ arity d`.
-/

namespace QuantumLTF.Membership.Supplement

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement.LcgSym54 Thm49Primitives Thm410Router Cslib.BitonicSort

/-- Bundled `gates12` Harmonic-Bucket 2-Sort stabilizer-subgroup state-prep circuit for NSILs
with `(L + d) ^ K_hl` logarithmic polylog factor. -/
structure HarmBucketHL54V2 where
  C_hl : ℝ
  C_hl_pos : 0 < C_hl
  K_hl : ℕ
  harmBucketAnc : ℕ → ℕ → ℕ → ℕ
  harmBucketH_lCircuit :
    (n K d : ℕ) → 1 ≤ n → 1 ≤ K → 1 ≤ d → 2 * K ≤ arity d →
      let s := Nat.clog 2 n + 1
      LayeredCircuit ((2 * K * s + arity d * d) + harmBucketAnc n K d)
  harmBucketH_lCircuit_size :
    ∀ (n K d : ℕ) (h1n : 1 ≤ n) (h1K : 1 ≤ K) (h1d : 1 ≤ d) (hNM : 2 * K ≤ arity d),
      let s := Nat.clog 2 n + 1
      let L := Nat.clog 2 ((K + 1) * (n + 1) + 2) + 1
      ((harmBucketH_lCircuit n K d h1n h1K h1d hNM).size : ℝ) ≤
        C_hl * ((K * s + arity d : ℕ) : ℝ) * ((L + d : ℕ) : ℝ) ^ K_hl
  act_harmBucketH_lCircuit :
    ∀ (n K d : ℕ) (h1n : 1 ≤ n) (h1K : 1 ≤ K) (h1d : 1 ≤ d) (hNM : 2 * K ≤ arity d)
      (l : Fin (2 * K) → Fin (n + 1)), Monotone l →
      let s := Nat.clog 2 n + 1
      act (harmBucketH_lCircuit n K d h1n h1K h1d hNM).unitary
          (ket (padZero (2 * K * s + arity d * d) (harmBucketAnc n K d)
            (Fin.append (flatReg (2 * K) s fun p => particleSym54 n s (l p)) (fun _ => false)))) =
        ((1 / Real.sqrt (Fintype.card (stabGroup (2 * K) l) : ℝ) : ℝ) : ℂ) •
          ∑ h : stabGroup (2 * K) l,
            ket (padZero (2 * K * s + arity d * d) (harmBucketAnc n K d)
              (Fin.append (flatReg (2 * K) s fun p => particleSym54 n s (l p))
                (flatReg (arity d) d (permRegBits (2 * K) d hNM h.1))))

end QuantumLTF.Membership.Supplement


