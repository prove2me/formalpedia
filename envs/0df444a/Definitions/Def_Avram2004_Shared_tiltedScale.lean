-- Prove2me | Definitions.Def_Avram2004_Shared_tiltedScale
-- name    : Avram2004_Shared_tiltedScale
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:18:55.856236+00:00
-- url     : https://prove2.me/theorems/d732db32-a54e-4c4d-b873-3353a91d6fa5
-- title:
--   Laplace exponent ψ, tilted exponent ψ_v, and the tilted scale functions W_v^(p), Z_v^(p)
-- statement:
--   Let $X$ be a process on $(\Omega,\mathcal F,\mathbb P)$.
--
--   1. The **Laplace exponent** (2) is $\psi(\theta)=\log\mathbb E[e^{\theta X_1}]$.
--   2. The **tilted exponent** (4) is $\psi_c(\theta)=\psi(\theta+c)-\psi(c)$: it is the Laplace exponent of $X$ under the Esscher measure $\mathbb P^c$ with $d\mathbb P^c/d\mathbb P|_{\mathcal F_t}=\exp(cX_t-\psi(c)t)$.
--   3. For real $v$ and $p$, $W_v^{(p)}$ is the $p$-scale function of the exponent $\psi_v$ (Definition 2 for $p\ge0$, the series (5) for $p<0$), and
--   $$Z_v^{(p)}(x)=1+p\int_{-\infty}^xW_v^{(p)}(z)\,dz .$$
--   With $v=0$ the tilt is $\psi$ itself, so $W^{(q)}=W_0^{(q)}$ and $Z^{(q)}=Z_0^{(q)}$ are the untilted scale functions.
--
--   These are the functions in which Theorem 1 is written, with $p=u-\psi(v)$. In the Russian and Canadized Russian problems only the untilted $W^{(q)}$, $Z^{(q)}$ of $(X,\mathbb P)$ occur in the final formulas; the tilted ones appear in Remark 4, which converts between them.
--
--   **Formalization Note** Mathlib's cumulant generating function is used for $\psi$; it takes the value $0$ when $e^{\theta X_1}$ is not integrable, so every statement that uses $\psi(v)$ assumes explicitly that $e^{vX_1}$ is integrable (the paper's "$\psi(v)<\infty$"). Definition 2 depends on the process only through its exponent, and $\psi_v$ is the exponent of $X$ under $\mathbb P^v$, so $W_v^{(p)}$ ("the scale function of $(X,\mathbb P^v)$") is defined from $\psi_v$ without constructing $\mathbb P^v$. The identity $W^{(u)}(x)=e^{vx}W_v^{(u-\psi(v))}(x)$ (Remark 4) is not built into the definition: it is a separate theorem.
--
--   **Shared definition.** This is the group's single copy of this definition, reviewed once for every chunk that uses it: `01-reflected-exit` (Theorem 1: Eq. (2) p. 216, Remark 4 p. 218, Proposition 1 p. 219, Theorem 1 and its proof pp. 220–224, Remark 6 p. 225); `02-russian` (Theorem 2: Remarks 3–4 and Lemma 1 p. 218, the Russian problem (27)–(28) pp. 227–228, Corollary 1 p. 228, Lemma 2 and Theorem 2 p. 229, proof of Theorem 2 pp. 230–231); `03-canadized-russian` (Theorem 3: Corollary 1 p. 228, Lemma 2 (i) p. 229, the Canadized problem (32) and Lemma 3 pp. 231–233, Theorem 3 p. 233, Lemma 4 p. 234, proof of Theorem 3 pp. 234–235).
-- source:
--   Avram, Kyprianou, Pistorius, Exit problems for spectrally negative Lévy processes and applications to (Canadized) Russian options, Ann. Appl. Probab. 14(1), 2004, pp. 216–218, Eq. (2), Remark 1 Eq. (4), Definition 2 (notation W_c), Eq. (5), Definition 3

import Mathlib
import Definitions.Def_Avram2004_Shared_scaleFun

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Avram2004.Shared

/-- The Laplace exponent (2): `ψ(θ) = log 𝔼[e^{θ X_1}]`. (Mathlib's `cgf` is `0` when `e^{θX_1}` is not
integrable, so every statement using `ψ(v)` assumes that integrability explicitly.) -/
noncomputable def psi {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ)
    (θ : ℝ) : ℝ :=
  cgf (X 1) P θ

/-- The tilted exponent (4): `ψ_c(θ) = ψ(θ + c) - ψ(c)`, the Laplace exponent of `X` under the Esscher
measure `ℙ^c`. -/
noncomputable def tilt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ)
    (c : ℝ) : ℝ → ℝ :=
  fun θ => psi P X (θ + c) - psi P X c

/-- `W_v^{(p)}`: the `p`-scale function of `(X, ℙ^v)` for every real `p` (Definition 2 for `p ≥ 0`,
the series (5) for `p < 0`). `W P X 0 q` is the untilted `W^{(q)}`. -/
noncomputable def W {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ)
    (v p : ℝ) : ℝ → ℝ :=
  scaleFunExt (tilt P X v) p

/-- `Z_v^{(p)}(x) = 1 + p ∫_{-∞}^x W_v^{(p)}(z) dz` (Definition 3 and its extension). `Z P X 0 q` is the
untilted `Z^{(q)}`. -/
noncomputable def Z {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ)
    (v p : ℝ) : ℝ → ℝ :=
  scaleZ (tilt P X v) p

end Avram2004.Shared


