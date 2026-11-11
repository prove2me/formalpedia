-- Prove2me | Definitions.Def_UnitaryQIPPSPACE_PSPACEComputableFam
-- name    : UnitaryQIPPSPACE_PSPACEComputableFam
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:34:30.156228+00:00
-- url     : https://prove2.me/theorems/7f394416-c37d-4465-80e4-4c9e53108852
-- title:
--   PSPACE-computable complex numbers and matrix entries (Definition 2.4)
-- statement:
--   A family $\{\alpha_x\}_{x\in I}$ of complex numbers is **PSPACE-computable** if a deterministic Turing machine, on input $x$ and unary precision $1^h$, outputs a pair of dyadic rationals $(a,b)$ with $|a+ib-\alpha_x|\le2^{-h}$ using $\mathrm{poly}(|x|+h)$ space. A matrix family $\{W_n\}$ ($2^n\times2^n$) **has PSPACE-computable entries** if the family $\{\langle i|W_n|j\rangle\}_{(1^n,i,j)}$ is PSPACE-computable.
--
--   These numbers connect polynomial-space synthesis with synthesis relative to a PSPACE oracle (Proposition 4.5, Lemma 4.7).
--
--   **Formalization Note** The family is indexed by a type with an injective encoding into strings; $(1^n,i,j)$ is the tuple code of $1^n$ and the bit strings $i,j$. The running time is unbounded; dyadic rationals are written as $1^k0s\,m_0m_1\cdots$ (fraction bits, sign, little-endian magnitude).
-- source:
--   He, Ou, Zhao, unitaryQIP = unitaryPSPACE, arXiv:2611.02819 (held version, sha256 9e357a00…ead793), Definition 2.4, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity
import Definitions.Def_QAdvFew_PoQOracle_OTM
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_UnitaryQIPPSPACE_Bits
import Definitions.Def_UnitaryQIPPSPACE_SpaceUniform

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace UnitaryQIPPSPACE

/-- **Dyadic rational of a bit string**: `1^k 0 s m₀ m₁ ⋯ m_r` denotes
`(−1)^s (m₀ + 2 m₁ + ⋯ + 2^r m_r) / 2^k` (`k` fraction bits, a sign bit, the magnitude in
little-endian binary); a string without the `0` ending the prefix or without a sign bit denotes `0`.
Every dyadic rational has such a code. -/
def dyadic (s : Str) : ℚ :=
  let k := (s.takeWhile id).length
  match s.drop (k + 1) with
  | [] => 0
  | sgn :: mag => (if sgn then -1 else 1) * (Nat.ofDigits 2 (mag.map Bool.toNat) : ℚ) / 2 ^ k

/-- **PSPACE-computable family of complex numbers** (He, Ou, Zhao, *unitaryQIP = unitaryPSPACE*,
arXiv:2611.02819, held version sha256 9e357a00…, Definition 2.4, p. 10 (PDF p. 12)): "Let
`I ⊆ {0,1}*`. A family `{α_x}_{x ∈ I}` of complex numbers is PSPACE-computable if there exists a
deterministic Turing machine, on input `x ∈ I` and unary precision `1^h`, outputs a pair of dyadic
rationals `(a, b)` subject to `|a + ib − α_x| ≤ 2^{−h}` using `poly(|x| + h)` space."

The family is indexed by a type `J` with an encoding `enc : J → {0,1}*` (the index set is
`I = enc(J)`). One machine `M` and one polynomial `p`: for every index `x` and precision `h`, the
run of `M` on `tup [enc x, 1^h]` halts after visiting at most `p(|enc x| + h)` cells, with output
`tup [a, b]`, and the dyadic rationals `a, b` satisfy `|a + ib − α_x| ≤ 2^{−h}`.

**Formalization Note** Machines are the published `QAdvFew.PoQOracle.OTM` with the empty oracle;
the running time is not bounded. Dyadic rationals are written in the format of `dyadic`. -/
def PSPACEComputableFam {J : Type} (enc : J → Str) (α : J → ℂ) : Prop :=
  ∃ (M : OTM) (p : Polynomial ℕ), ∀ (x : J) (h : ℕ), ∃ T : ℕ,
    M.result noOracle (tup [enc x, unary h]) T ≠ none ∧
    M.space noOracle (tup [enc x, unary h]) T ≤ p.eval ((enc x).length + h) ∧
    ∃ a b : Str, M.output noOracle (tup [enc x, unary h]) T = tup [a, b] ∧
      ‖(((dyadic a : ℚ) : ℝ) : ℂ) + (((dyadic b : ℚ) : ℝ) : ℂ) * Complex.I - α x‖ ≤ (1 / 2 : ℝ) ^ h

/-- **A matrix family with PSPACE-computable entries** (Definition 2.4, p. 10): "We say that a
unitary family `{W_n}`, where each `W_n` is a `d_n × d_n` matrix, has PSPACE-computable entries if
the family `{⟨i|W_n|j⟩}_{(1^n, i, j)}` with `i, j ∈ [d_n]` is PSPACE-computable." Here
`d_n = 2^n`, and `(1^n, i, j)` is encoded as `tup [1^n, i, j]` with the bit strings `i, j`. -/
def HasPSPACEEntries (W : (n : ℕ) → Matrix (Bits n) (Bits n) ℂ) : Prop :=
  PSPACEComputableFam (J := Σ n : ℕ, Bits n × Bits n)
    (fun x => tup [unary x.1, x.2.1.toStr, x.2.2.toStr]) (fun x => W x.1 x.2.1 x.2.2)

end UnitaryQIPPSPACE


