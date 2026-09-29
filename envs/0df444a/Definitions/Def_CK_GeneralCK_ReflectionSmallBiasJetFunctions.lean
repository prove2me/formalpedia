-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionSmallBiasJetFunctions
-- name    : CK_GeneralCK_ReflectionSmallBiasJetFunctions
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T15:47:13.85479+00:00
-- url     : https://prove2.me/theorems/e15af23c-ebda-4f98-a3c0-95fc043a3cd3
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionSmallBiasJetFunctions` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionSmallBiasJetFunctions` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionSmallBiasJetFunctions` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionSmallBiasJetFunctions (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionSmallBiasJetFunctions.lean)

import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasJetInverse
import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasPicard

-- ===== source module GeneralCK.ReflectionSmallBiasJetFunctions =====
section

/-! # Entropy, atanh and finite contact iteration in the Taylor verifier -/

namespace GeneralCK.Reflection.SmallBiasPolynomial

def entropy (n : ℕ) (p : List Term) : List Term :=
  add (parameter 1) (scale (-1 / 2)
    (add (mulTrunc n (add (const 1) p) (logOneAdd n p))
      (mulTrunc n (add (const 1) (scale (-1) p)) (logOneAdd n (scale (-1) p)))))

def atanh (n : ℕ) (p : List Term) : List Term :=
  scale (1 / 2) (add (logOneAdd n p) (scale (-1) (logOneAdd n (scale (-1) p))))

def picard (n : ℕ) : ℕ → List Term
  | 0 => const 0
  | m + 1 => mulTrunc n coordinateA (entropy n (picard n m))

end GeneralCK.Reflection.SmallBiasPolynomial

namespace GeneralCK.Reflection.SmallBiasJet.Approximates

open Filter Asymptotics SmallBiasPolynomial
open scoped Topology

theorem entropy {n : ℕ} {k : ℂ} {f : ℂ × ℂ → ℂ} {p : List Term}
    (hk : k ≠ 0) (hklog : k = (Real.log 2 : ℂ))
    (hf : Approximates (n + 1) k f p) (hzero : f 0 = 0) :
    Approximates (n + 1) k (fun z => ComplexEntropy.entropyExt (f z))
      (SmallBiasPolynomial.entropy (n + 1) p) := by
  have hneg := hf.scale (-1)
  have hneg0 : (fun z => ((-1 : ℚ) : ℂ) * f z) 0 = 0 := by simp [hzero]
  have hplus := (const (n + 1) k 1).add hf
  have hminus := (const (n + 1) k 1).add hneg
  have hp := hplus.mul hk (hf.logOneAdd hk hzero)
  have hm := hminus.mul hk (hneg.logOneAdd hk hneg0)
  have hh := (parameter (n + 1) k 1).add ((hp.add hm).scale (-1 / 2))
  convert hh using 1
  · funext z
    simp only [ComplexEntropy.entropyExt, hklog, zpow_one, Rat.cast_one,
      Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat, neg_one_mul, ← sub_eq_add_neg]
    ring
  · rfl

theorem atanh {n : ℕ} {k : ℂ} {f : ℂ × ℂ → ℂ} {p : List Term}
    (hk : k ≠ 0) (hf : Approximates (n + 1) k f p) (hzero : f 0 = 0) :
    Approximates (n + 1) k (fun z => SmallBiasComplexDomain.atanhExt (f z))
      (SmallBiasPolynomial.atanh (n + 1) p) := by
  have hneg := hf.scale (-1)
  have hneg0 : (fun z => ((-1 : ℚ) : ℂ) * f z) 0 = 0 := by simp [hzero]
  have hh := ((hf.logOneAdd hk hzero).add ((hneg.logOneAdd hk hneg0).scale (-1))).scale (1 / 2)
  convert hh using 1
  · funext z
    simp only [SmallBiasComplexDomain.atanhExt, Rat.cast_one, Rat.cast_neg,
      Rat.cast_div, Rat.cast_ofNat, neg_one_mul, ← sub_eq_add_neg]
    ring
  · rfl

theorem picard {n : ℕ} {k : ℂ} (hk : k ≠ 0) (hklog : k = (Real.log 2 : ℂ)) (m : ℕ) :
    Approximates (n + 1) k (fun z => SmallBiasPicard.iterate m z.1)
      (SmallBiasPolynomial.picard (n + 1) m) := by
  induction m with
  | zero => simpa only [SmallBiasPicard.iterate, SmallBiasPolynomial.picard, Rat.cast_zero]
      using const (n + 1) k 0
  | succ m ih =>
    exact (coordinateA (n + 1) k).mul hk (ih.entropy hk hklog (by simp))

end GeneralCK.Reflection.SmallBiasJet.Approximates

end


