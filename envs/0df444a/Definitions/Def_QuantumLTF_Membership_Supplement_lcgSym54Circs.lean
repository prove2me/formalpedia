-- Prove2me | Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54Circs
-- name    : QuantumLTF_Membership_Supplement_lcgSym54Circs
-- status  : Definition
-- author  : @Robin Kothari
-- created : 2026-11-25T03:06:02.031822+00:00
-- url     : https://prove2.me/theorems/1d85040c-a94d-483c-bf9d-294c8479e060
-- title:
--   Alonso–Schott SIL conversion and Harmonic-Bucket stabilizer state-preparation circuits ($\mathrm{AlonsoSchottSil54}$, $\mathrm{HarmBucketHL54}$)
-- statement:
--   Defines the padded permutation register encodings `padZeroLESBits` and `permRegBits`, together with two modular `gates12` (`LayeredCircuit`) sub-circuit suites used to assemble Stage B NSIL symmetrization (`nsil_symmetrize_54`):
--
--   1. **Alonso–Schott SIL Suite (`AlonsoSchottSil54`):** Provides the in-place reversible conversion `alonsoSchottCircuit` mapping $|s^\sigma, 0^{\mathrm{anc}}\rangle \mapsto |\sigma^{-1}(0\dots M-1), 0^{\mathrm{anc}}\rangle$ for $\sigma \in S_N$ and the uniform symmetric-group synthesis circuit `unifPermCircuit` preparing
--
--   $$
--   |0\rangle \longmapsto \frac{1}{\sqrt{N!}} \sum_{\sigma \in S_N} \bigl|\mathrm{padPerm}_{N,M}(\sigma)(0\dots M-1)\bigr\rangle
--   $$
--
--   in $O(M (d+1)^4)$ `gates12` gates ($M = 2^d \ge N$).
--
--   2. **Harmonic-Bucket Stabilizer Suite (`HarmBucketHL54`):** Controlled on any monotone non-strictly increasing list $|l\rangle_1$ in `{0, ..., n-1, \bot}^{2K}$, provides `harmBucketH_lCircuit` preparing
--
--   $$
--   |l\rangle |0\rangle \longmapsto |l\rangle \otimes \frac{1}{\sqrt{|H_l|}} \sum_{h \in H_l} \bigl|\mathrm{padPerm}_{2K, M}(h)(0\dots M-1)\bigr\rangle
--   $$
--
--   with $O\bigl((K s + M)\, (\lceil \log_2((K+1)(n+1)+2) \rceil + 1)^{K_{\mathrm{hl}}}\bigr)$ `gates12` gates via Harmonic-Bucket $2$-Sort routing and in-place Alonso–Schott conversion.
--
--   **Formalization Note** Both structures are proved inhabited by `alonso_schott_sil_54` and `harm_bucket_hl_54`.
-- source:
--   Alonso and Schott (1995), Random Generation of Trees; Liu, Childs, Gottesman [LCG26], First and second quantization: reversible and quantum circuits (arXiv:2411.04019, Section IV); Krivcenko, Nguyen, de Wolf [KNW26] (arXiv:2609.40331, Theorem 5.4).

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

set_option autoImplicit false

/-!
# `[LCG26]` Stage B Sub-Circuit Interfaces (`AlonsoSchottSil54`, `HarmBucketHL54`)

Defines the register-encoding helper functions (`padZeroLESBits`, `permRegBits`) and the two
bundled `gates12` circuit interfaces used to assemble `QuantumLTF.Membership.Supplement.nsil_symmetrize_54`:
1. `AlonsoSchottSil54`: in-place reversible Alonso–Schott conversion `|padLES⟩ ↦ |padPerm (lesToPerm s)⁻¹⟩`
   and uniform symmetric-group superposition synthesis `|0⟩ ↦ (1/√N!) ∑_{σ ∈ S_N} |padPerm σ⟩`.
2. `HarmBucketHL54`: controlled uniform stabilizer-subgroup superposition synthesis
   `|l⟩|0⟩ ↦ (1/√|H_l|) ∑_{h ∈ H_l} |l⟩|padPerm h⟩` via Harmonic-Bucket 2-Sort routing and
   in-place Alonso–Schott conversion.
-/

namespace QuantumLTF.Membership.Supplement.LcgSym54

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement Thm49Primitives Thm410Router Cslib.BitonicSort

/-- Encodes a 0-based LES `s : Fin N → ℕ` on `arity d` registers of width `d` (`N ≤ arity d`),
zero-padding slots `p ≥ N`. -/
def padZeroLESBits (N d : ℕ) (s : Fin N → ℕ) (p : Fin (arity d)) : Qubits d :=
  if h : p.1 < N then natToBits d (s ⟨p.1, h⟩) else fun _ => false

/-- Encodes a padded permutation `padPerm54 N (arity d) hNM σ` on `arity d` registers of width `d`. -/
def permRegBits (N d : ℕ) (hNM : N ≤ arity d) (σ : Equiv.Perm (Fin N))
    (p : Fin (arity d)) : Qubits d :=
  natToBits d (padPerm54 N (arity d) hNM σ p).1

end QuantumLTF.Membership.Supplement.LcgSym54

namespace QuantumLTF.Membership.Supplement

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement.LcgSym54 Thm49Primitives Thm410Router Cslib.BitonicSort

/-- Bundled `gates12` Alonso–Schott LES-to-permutation & uniform `S_N` state-prep suite. -/
structure AlonsoSchottSil54 where
  C_as : ℝ
  C_as_pos : 0 < C_as
  alonsoSchottAnc : ℕ → ℕ → ℕ
  alonsoSchottCircuit :
    (N d : ℕ) → 1 ≤ N → 1 ≤ d → N ≤ arity d →
      LayeredCircuit (arity d * d + alonsoSchottAnc N d)
  alonsoSchottCircuit_size :
    ∀ (N d : ℕ) (h1N : 1 ≤ N) (h1d : 1 ≤ d) (hNM : N ≤ arity d),
      ((alonsoSchottCircuit N d h1N h1d hNM).size : ℝ) ≤
        C_as * (arity d : ℝ) * ((d + 1 : ℕ) : ℝ) ^ 4
  act_alonsoSchottCircuit :
    ∀ (N d : ℕ) (h1N : 1 ≤ N) (h1d : 1 ≤ d) (hNM : N ≤ arity d) (σ : Equiv.Perm (Fin N)),
      act (alonsoSchottCircuit N d h1N h1d hNM).unitary
          (ket (padZero (arity d * d) (alonsoSchottAnc N d)
            (flatReg (arity d) d (padZeroLESBits N d (permToLES N σ))))) =
        ket (padZero (arity d * d) (alonsoSchottAnc N d)
          (flatReg (arity d) d (permRegBits N d hNM σ⁻¹)))
  unifPermAnc : ℕ → ℕ → ℕ
  unifPermCircuit :
    (N d : ℕ) → 1 ≤ N → 1 ≤ d → N ≤ arity d →
      LayeredCircuit (arity d * d + unifPermAnc N d)
  unifPermCircuit_size :
    ∀ (N d : ℕ) (h1N : 1 ≤ N) (h1d : 1 ≤ d) (hNM : N ≤ arity d),
      ((unifPermCircuit N d h1N h1d hNM).size : ℝ) ≤
        C_as * (arity d : ℝ) * ((d + 1 : ℕ) : ℝ) ^ 4
  act_unifPermCircuit :
    ∀ (N d : ℕ) (h1N : 1 ≤ N) (h1d : 1 ≤ d) (hNM : N ≤ arity d),
      act (unifPermCircuit N d h1N h1d hNM).unitary (ket (fun _ => false)) =
        ((1 / Real.sqrt (Nat.factorial N : ℝ) : ℝ) : ℂ) •
          ∑ σ : Equiv.Perm (Fin N),
            ket (padZero (arity d * d) (unifPermAnc N d)
              (flatReg (arity d) d (permRegBits N d hNM σ)))

/-- Bundled `gates12` Harmonic-Bucket 2-Sort stabilizer-subgroup state-prep circuit for NSILs. -/
structure HarmBucketHL54 where
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
        C_hl * ((K * s + arity d : ℕ) : ℝ) * (L : ℝ) ^ K_hl
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


