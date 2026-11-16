-- Prove2me | Definitions.Def_CompDesign_Supplement_IsCCEOf
-- name    : CompDesign_Supplement_IsCCEOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T20:48:57.14165+00:00
-- url     : https://prove2.me/theorems/e2ed5b77-46fe-4f18-8a0a-21d6a6bc3eae
-- title:
--   Coarse correlated equilibrium $\mu\in\Delta(2^N)$ of a binary participation game
-- statement:
--   A distribution on participation profiles is a weight function $\mu:2^N\to\mathbb R$ with $\mu(S)\ge 0$ and $\sum_S\mu(S)=1$; write $\mathbb E_{S\sim\mu}[f(S)]=\sum_S\mu(S)f(S)$. For a payment rule $p$ and costs $c$, $\mu$ is a **coarse correlated equilibrium** if for every agent $i$ and each fixed deviation $a'_i\in\{\text{in},\text{out}\}$,
--   $$\mathbb E_{S\sim\mu}[u_i(S)]\ \ge\ \mathbb E_{S\sim\mu}[u_i(a'_i,S_{-i})],$$
--   where the deviation "in" yields $p_i(S\cup\{i\})-c_i$ and the deviation "out" yields $0$.
--
--   This is Definition 3.2 with $\epsilon=0$; it is the equilibrium notion of Theorems 5.5–5.9 and C.1.
--
--   **Formalization Note** $2^N$ is the finite type `Finset (Fin n)`, so weight functions are all of $\Delta(2^N)$.
-- source:
--   Anagnostides, Bhawalkar, Liaw, Mehta, Paes Leme, Teng, Velegkas, Zheng, Compensation Design, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…), Definition 3.2, p.14 (PDF 17)

import Mathlib
import Definitions.Def_CompDesign_Supplement_IsPNEOf

namespace CompDesign.Supplement

/-- A probability distribution on `2^N` (the finite set of participation profiles), as a weight
function: nonnegative weights summing to one (Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026,
sha256 3d305d4d…), Definition 3.2, p.14, PDF 17: `μ ∈ Δ(2^N)`). -/
def IsDistribution {n : ℕ} (μ : Finset (Fin n) → ℝ) : Prop :=
  (∀ S, 0 ≤ μ S) ∧ ∑ S, μ S = 1

/-- The expectation `E_{S∼μ}[f(S)] = ∑_S μ(S) f(S)` over the finite set `2^N`. -/
def expect {n : ℕ} (μ : Finset (Fin n) → ℝ) (f : Finset (Fin n) → ℝ) : ℝ :=
  ∑ S, μ S * f S

/-- A coarse correlated equilibrium (`ε = 0`) of the binary participation game induced by a
general payment rule `p` at costs `c` (Definition 3.2, p.14, PDF 17, of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026,
sha256 3d305d4d…)): for every agent `i`
and each fixed deviation `a′_i ∈ {in, out}`, `E_μ[u_i(S)] ≥ E_μ[u_i(a′_i, S_{−i})]`. The deviation
"in" yields `p_i(S ∪ {i}) − c_i`, the deviation "out" yields `0`.

**Formalization Note.** `μ` is a weight function on the finite set `Finset (Fin n)`, which is all of
`Δ(2^N)`. -/
def IsCCEOf {n : ℕ} (p : Finset (Fin n) → Fin n → ℝ) (c : Fin n → ℝ)
    (μ : Finset (Fin n) → ℝ) : Prop :=
  IsDistribution μ ∧ ∀ i : Fin n,
    expect μ (fun S => p (insert i S) i - c i) ≤ expect μ (fun S => utilOf p c S i) ∧
      0 ≤ expect μ (fun S => utilOf p c S i)

end CompDesign.Supplement


