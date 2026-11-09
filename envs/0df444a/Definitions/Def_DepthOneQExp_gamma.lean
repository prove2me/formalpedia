-- Prove2me | Definitions.Def_DepthOneQExp_gamma
-- name    : DepthOneQExp_gamma
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:44:12.668513+00:00
-- url     : https://prove2.me/theorems/ab01423a-1ce1-477e-8356-3e32f5c782eb
-- title:
--   The representation $\Gamma: \mathrm{SL}(n;\mathbb F_2)\to\mathrm{Sym}(2^n)$
-- statement:
--   Every $g\in\mathrm{SL}(n;\mathbb F_2)$ acts linearly on $\mathbb F_2^n$ and therefore permutes the $2^n$ bit strings. This gives the representation (Eqs. (2.7)–(2.8))
--   $$
--   \Gamma(g)\,|x\rangle = |g\cdot x\rangle, \qquad x\in\mathbb F_2^n .
--   $$
--   Here $\Gamma$ is a group homomorphism into the permutations of $\{0,1\}^n$; the unitary of $\Gamma(g)$ is its permutation matrix.
--
--   **Formalization Note** The paper's $\Gamma$ lands in $U(2^n)$; composing with `permToMatrix` recovers it. Bit $i$ is the paper's coordinate $i+1$.
-- source:
--   Anshu–Balasubramanian–Haferkamp–Harrow–Tan, Depth-1 expanders on the unitary group and applications, arXiv:2609.01605 (held version, sha256 3c3f8513…aebfd87), Eqs. (2.7)–(2.8), p.7

import Mathlib
import Definitions.Def_MITMSynthesis_Gate

namespace DepthOneQExp

/-- The representation `Γ : SL(n; 𝔽₂) → Sym(2ⁿ)` by which `g` permutes the computational basis,
`Γ(g)|x⟩ = |g·x⟩` (Anshu–Balasubramanian–Haferkamp–Harrow–Tan, *Depth-1 expanders on the unitary
group and applications*, arXiv:2609.01605, held version sha256 3c3f8513…aebfd87, Eqs. (2.7)–(2.8),
p.7).

**Formalization Note** The paper's `Γ` lands in `U(2ⁿ)`; here it lands in the permutations of the
basis `{0,1}ⁿ = Fin n → Fin 2` (which equals `Fin n → ZMod 2`), and its unitary is
`permToMatrix (gamma n g)`. Bit `i` is the paper's coordinate `i + 1`. -/
def gamma (n : ℕ) :
    Matrix.SpecialLinearGroup (Fin n) (ZMod 2) →* Equiv.Perm (MITMSynthesis.Q n) where
  toFun g := (Matrix.SpecialLinearGroup.toLin' g).toEquiv
  map_one' := by
    ext x i
    simp only [map_one]
    rfl
  map_mul' g h := by
    ext x i
    simp only [map_mul]
    rfl

end DepthOneQExp


