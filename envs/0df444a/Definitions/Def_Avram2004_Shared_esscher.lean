-- Prove2me | Definitions.Def_Avram2004_Shared_esscher
-- name    : Avram2004_Shared_esscher
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T20:04:17.115136+00:00
-- url     : https://prove2.me/theorems/2e644255-7723-417a-8797-eb8e8bbfd253
-- title:
--   The Esscher measure ℙ¹: dℙ¹/dℙ restricted to 𝓕_t equals exp(X_t − r t)
-- statement:
--   Let $(\Omega,\mathcal F,\mathbf F,\mathbb P)$ be a filtered probability space, $X$ an adapted real process with $X_0=0$, and $r\in\mathbb R$. A measure $\mathbb Q$ on $(\Omega,\mathcal F)$ is the **Esscher measure** $\mathbb P^1$ (with parameter $r$) if for every $t\ge0$ its restriction to $\mathcal F_t$ has density $e^{X_t-rt}$ with respect to the restriction of $\mathbb P$:
--   $$\frac{d\mathbb P^1}{d\mathbb P}\Big|_{\mathcal F_t}=\exp(X_t-rt),\qquad t\ge0 .$$
--
--   This is the paper's change of measure (3) with $c=1$, where $r=\psi(1)=\log\mathbb E[e^{X_1}]$ (in the Russian option model the risk-neutral assumption forces $\psi(1)=r$). Under $\mathbb P^1$ the process $X$ is again a spectrally negative Lévy process, with Laplace exponent $\psi_1(\theta)=\psi(\theta+1)-\psi(1)$. The expectation $\mathbb E^1_{-z}$ of the Russian problem (28) is the expectation under $\mathbb P^1$ of functionals of the reflected process started at $Y_0=z$.
--
--   **Formalization Note** $\mathbb P^1$ is taken as data (a measure $\mathbb Q$) together with this defining relation, stated as equality of the restrictions (`trim`) of $\mathbb Q$ and of $e^{X_t-rt}\cdot\mathbb P$ to $\mathcal F_t$ for every $t$. It is not constructed: its existence on a path space is a theorem, not a definition. The relation at $t=0$ forces $\mathbb Q$ and $\mathbb P$ to agree on $\mathcal F_0$, which is why the filtration is not completed.
--
--   **Shared definition.** This is the group's single copy of this definition, reviewed once for every chunk that uses it: `02-russian` (Theorem 2: Remarks 3–4 and Lemma 1 p. 218, the Russian problem (27)–(28) pp. 227–228, Corollary 1 p. 228, Lemma 2 and Theorem 2 p. 229, proof of Theorem 2 pp. 230–231); `03-canadized-russian` (Theorem 3: Corollary 1 p. 228, Lemma 2 (i) p. 229, the Canadized problem (32) and Lemma 3 pp. 231–233, Theorem 3 p. 233, Lemma 4 p. 234, proof of Theorem 3 pp. 234–235).
-- source:
--   Avram, Kyprianou, Pistorius, Exit problems for spectrally negative Lévy processes and applications to (Canadized) Russian options, Ann. Appl. Probab. 14(1), 2004, p. 216, Section 2, Eq. (3) (with c = 1), and p. 227, §5 ("this necessarily implies that ψ(1) = r")

import Mathlib

open MeasureTheory
open scoped NNReal ENNReal

namespace Avram2004.Shared

/-- The Esscher measure `ℙ^1` of (3), p. 217: a measure `Q` on `Ω` with
`dQ/dP |_{𝓕_t} = exp(X_t - r t)` for every `t ≥ 0`, where `r = ψ(1)`. Stated as the equality of the
restrictions of `Q` and of `e^{X_t - rt} · P` to the σ-algebra `𝓕_t`, for every `t`. -/
def IsEsscher {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m) (P Q : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ) (r : ℝ) : Prop :=
  ∀ t : ℝ≥0, Q.trim (𝓕.le t) =
    (P.withDensity (fun ω => ENNReal.ofReal (Real.exp (X t ω - r * (t : ℝ))))).trim (𝓕.le t)

end Avram2004.Shared


