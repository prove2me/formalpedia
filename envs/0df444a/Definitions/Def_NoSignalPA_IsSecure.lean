-- Prove2me | Definitions.Def_NoSignalPA_IsSecure
-- name    : NoSignalPA_IsSecure
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:04:51.730992+00:00
-- url     : https://prove2.me/theorems/f71f8ec3-6393-45af-a72e-2a2eadd05946
-- title:
--   A hash function $h$ satisfying the security bound (5) for every nonsignaling box
-- statement:
--   A hash function $h:\{0,1\}^{N_r}\to\{0,1\}^{N_s}$ is **secure** when, for every choice of Eve's input and output sets $Z,E$, every $(N_r+2)$-partite nonsignaling box $P_{\mathbf a,\mathbf b,e|\mathbf x,\mathbf y,z}$, every input $\mathbf y$ of Bob and every input $z_0$ of Eve, the key $\mathbf k=h(\mathbf a)$ satisfies
--
--   $$
--   \sum_{\mathbf k}\ \sup_{z}\ \sum_{e}\Bigl|P_{\mathbf k,e|\mathbf x=\mathbf 0,z}-2^{-N_s}P_{e|z}\Bigr|\ \le\ \sqrt{2^{\,N_s+\sqrt{N_r}}}\ \langle\mathrm{CHSH}|^{\otimes N_r}|P_{\mathbf a,\mathbf b|\mathbf x,\mathbf y}\rangle ,
--   $$
--
--   where the key and Eve marginals are read at $\mathbf x=\mathbf 0$ and Bob's input $\mathbf y$, and $P_{\mathbf a,\mathbf b|\mathbf x,\mathbf y}$ is read at Eve's input $z_0$. The left side measures how well the real key can be told apart from an ideal key $2^{-N_s}P_{e|z}$ that is uniform and independent of Eve; the maximization over $z$ is inside the sum over $\mathbf k$, because Eve may choose her measurement after reading the key.
--
--   **Formalization Note** The supremum over $z$ and the sum over $e$ are taken in the extended nonnegative reals, so neither has a default value; each difference is computed in $\mathbb R$ before its absolute value is taken. $\sqrt2^{N_s+\sqrt{N_r}}$ is $\sqrt{2^{N_s+\sqrt{N_r}}}$, with a real exponent. $Z$ and $E$ range over all types of a fixed universe.
-- source:
--   Masanes, Universally-composable privacy amplification from causality constraints, arXiv:0807.2158v4, Main result, eq. (5), p.2

import Mathlib
import Definitions.Def_NoSignalPA_IsNonsignaling
import Definitions.Def_NoSignalPA_chshPow
import Definitions.Def_NoSignalPA_pairing
import Definitions.Def_NoSignalPA_abMarg
import Definitions.Def_NoSignalPA_keyEveMarg
import Definitions.Def_NoSignalPA_eveMarg

namespace NoSignalPA

open scoped ENNReal

/-- **A hash function satisfying the security bound (5) against every nonsignaling box.**
Ll. Masanes, *Universally-composable privacy amplification from causality constraints*,
arXiv:0807.2158v4, Main result, eq. (5), p. 2 (PDF p. 2): for an `(Nr + 2)`-partite nonsignaling
`P_{a,b,e|x,y,z}`, the key `k = h(a)` satisfies

`Σ_k max_z Σ_e |P_{k,e|x=0,z} − 2^{−Ns} P_{e|z}| ≤ √2^{Ns+√Nr} ⟨CHSH|^{⊗Nr} |P_{a,b|x,y}⟩`.

`IsSecure h` says this holds for **every** pair of types `Z, E` (Eve's inputs and outputs), every
nonsignaling box `P`, every Bob input `y` at which the key marginals are read and every Eve input
`z₀` at which `P_{a,b|x,y}` is read.

**Formalization Note.** (1) `max_z` is `⨆ z` in `ℝ≥0∞` (a maximum need not exist for infinite
`Z`), inside the sum over `k` ("the maximization on z depends on k", p. 2). `Σ_e` is a `tsum`
in `ℝ≥0∞`. Neither has a junk value. (2) Each difference is taken in `ℝ` and its absolute value
mapped to `ℝ≥0∞` by `ENNReal.ofReal`, so no truncated subtraction occurs. (3) `√2^{Ns+√Nr}` is
`√(2^{Ns+√Nr})` with a real power. (4) `x = 0` is the all-false string. (5) The type universe of
`Z, E` is a parameter of the predicate. -/
def IsSecure.{u} {Nr Ns : ℕ} (h : Str Nr → Str Ns) : Prop :=
  ∀ (Z E : Type u) (P : Box Nr Z E), IsNonsignaling P → ∀ (y : Str Nr) (z₀ : Z),
    ∑ k : Str Ns, ⨆ z : Z, ∑' e : E,
        ENNReal.ofReal |(keyEveMarg h P (fun _ => false) y z k e).toReal
          - ((2 : ℝ) ^ Ns)⁻¹ * (eveMarg P (fun _ => false) y z e).toReal|
      ≤ ENNReal.ofReal
          (Real.sqrt ((2 : ℝ) ^ ((Ns : ℝ) + Real.sqrt Nr)) * pairing chshPow (abMarg P z₀))

end NoSignalPA


