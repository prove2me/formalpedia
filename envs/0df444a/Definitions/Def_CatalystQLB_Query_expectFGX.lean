-- Prove2me | Definitions.Def_CatalystQLB_Query_expectFGX
-- name    : CatalystQLB_Query_expectFGX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:20:36.081796+00:00
-- url     : https://prove2.me/theorems/5040e0bf-1796-4805-b73f-eee9bcc80312
-- title:
--   Average over random functions $f,g$ and a uniform input $x$
-- statement:
--   For a real function $F(f,g,x)$ of two functions $f,g:\{0,1\}^\lambda\to\{0,1\}^\lambda$ and a string $x\in\{0,1\}^\lambda$, this is the expectation
--   $$\mathbb E_{f,g,x}\,F(f,g,x)=\frac{1}{|\{0,1\}^\lambda\to\{0,1\}^\lambda|^2\,2^\lambda}\sum_{f}\sum_{g}\sum_{x}F(f,g,x)$$
--   when $f$ and $g$ are independent uniformly random functions and $x$ is an independent uniform string.
--
--   Every success probability and advantage in the mission is such an average: the random oracles and the instance are drawn jointly.
--
--   **Formalization Note** `n` is the paper's $\lambda$; $|\{0,1\}^\lambda\to\{0,1\}^\lambda|=2^{\lambda 2^\lambda}$ is written as a `Fintype.card`.
-- source:
--   Arora, Chakraborty, Cojocaru, Saminathan, Singh, Computational Work Extraction: The Complexity of Catalysts, arXiv:2609.40323 (version of 2026-11-03, sha256 44854b3a…), §5.3, p.44 (PDF 47); Lemma 8, p.12 (PDF 15)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

namespace CatalystQLB.Query

open QAlgorithms

/-- The expectation `E_{f,g,x} F(f, g, x)` over two independent uniformly random functions
`f, g : {0,1}^n → {0,1}^n` and an independent uniform `x ∈ {0,1}^n` (Arora, Chakraborty, Cojocaru, Saminathan, Singh, *Computational Work Extraction: The Complexity of Catalysts*, arXiv:2609.40323 (version of 2026-11-03), §5.3, p.44
(PDF 47): "f, g : {0,1}^λ → {0,1}^λ are independent uniformly random functions, and
`x ∈ {0,1}^λ` is independently uniform"; Lemma 8, p.12 (PDF 15): "average success
probability").

**Formalization Note** The plain sum divided by `|{0,1}^n → {0,1}^n|² · 2^n`
(`|{0,1}^n → {0,1}^n| = 2^{n·2^n}`). `n` is the paper's `λ`. -/
noncomputable def expectFGX (n : ℕ) (F : (Qubits n → Qubits n) → (Qubits n → Qubits n) →
    Qubits n → ℝ) : ℝ :=
  ((Fintype.card (Qubits n → Qubits n) : ℝ) ^ 2 * 2 ^ n)⁻¹ * ∑ f, ∑ g, ∑ x, F f g x

end CatalystQLB.Query


