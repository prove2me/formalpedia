-- Prove2me | Definitions.Def_LatticePrepro_Conversions_ConstructionA_Ext
-- name    : LatticePrepro_Conversions_ConstructionA_Ext
-- status  : Definition
-- author  : @WizardOfMenlo
-- created : 2026-11-20T00:10:20.374766+00:00
-- url     : https://prove2.me/theorems/de239cb4-a313-4fc9-82e3-3449225965f9
-- title:
--   Construction A lattices and reduction modulo $p$ (Lemma B.1)
-- statement:
--   Fix a prime $p$ and a coordinate set $M$.
--
--   1. **Reduction modulo $p$** (`redMod`): the $\mathbb Z$-linear map $\mathbb Z^{M}\to\mathbb F_p^{M}$ that reduces every coordinate modulo $p$.
--   2. **Construction A** (`constructionA`): for a linear code $\mathcal C\subseteq\mathbb F_p^{M}$, the lattice
--   $$\Lambda_{\mathcal C}=\{v\in\mathbb Z^{M}: v \bmod p\in\mathcal C\}=\mathcal C+p\,\mathbb Z^{M}.$$
--
--   The bundle also contains two rewriting lemmas: the coordinates of the reduction (`redMod_apply`), and that the canonical lift of a word $y\in\mathbb F_p^{M}$ (with entries in $\{0,\dots,p-1\}$, `liftZMod`) reduces to $y$ (`redMod_liftZMod`).
--
--   This is the lattice of Lemma B.1, used in the lattice reduction of Lemma 3.12.
--
--   **Formalization Note.** `constructionA C` is a `Submodule ℤ (M → ℤ)`, defined as the preimage of $\mathcal C$, regarded as an additive subgroup, under reduction modulo $p$.
-- source:
--   G. Fenzi, G. Weissenberg, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847; IACR ePrint 2026/2634, https://eprint.iacr.org/2026/2634), Lemma B.1 (\label{lem:construction-a-gap}) in Appendix B.2 (\label{subsec:conversion-proof}); Lean: LatticePrepro/Conversions/ConstructionA.lean, LatticePrepro.redMod, LatticePrepro.constructionA

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Conversions_ConstructionA

/-! Further definitions from `LatticePrepro/Conversions/ConstructionA.lean`, continuing `Def_LatticePrepro_Conversions_ConstructionA`. -/

namespace LatticePrepro

open Finset

variable {p : ℕ} [Fact p.Prime] {M : Type*}

/-- Coordinatewise reduction modulo `p` as a `ℤ`-linear map. -/
def redMod (p : ℕ) (M : Type*) : (M → ℤ) →ₗ[ℤ] (M → ZMod p) :=
  LinearMap.pi fun i => (Int.castAddHom (ZMod p)).toIntLinearMap ∘ₗ LinearMap.proj i

@[simp] lemma redMod_apply (v : M → ℤ) (i : M) : redMod p M v i = (v i : ZMod p) := rfl

/-- The Construction A lattice `Λ_𝒞 = {v : v mod p ∈ 𝒞}`. -/
def constructionA (C : Submodule (ZMod p) (M → ZMod p)) : Submodule ℤ (M → ℤ) :=
  (C.restrictScalars ℤ).comap (redMod p M)

@[simp] lemma redMod_liftZMod (y : M → ZMod p) : redMod p M (liftZMod y) = y := by
  funext i
  simp [liftZMod]

end LatticePrepro


