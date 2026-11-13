-- Prove2me | Definitions.Def_SaglamGV_Fourier
-- name    : SaglamGV_Fourier
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:48:56.652165+00:00
-- url     : https://prove2.me/theorems/60a40745-59e1-4fd7-8c94-cc5d70b4e135
-- title:
--   Characters $\chi_y$, the unnormalized Fourier transform and uniform averages on $\mathbb F_2^n$
-- statement:
--   For $y\in\mathbb F_2^n$ the character is $\chi_y(x)=(-1)^{x\cdot y}$. The Fourier transform of $f:\mathbb F_2^n\to\mathbb R$ is the vector of coefficients
--
--   $$
--   \hat f(y)=\langle f,\chi_y\rangle=\sum_{x\in\mathbb F_2^n}f(x)\chi_y(x),
--   $$
--
--   with no normalizing factor (the paper notes it is $2^{n/2}$ times a unitary). $\mathbb E_y$ and $\Pr_y$ denote average and probability over $y$ uniform on $\mathbb F_2^n$. In particular
--
--   $$
--   \hat\mu(y)=\frac1V\sum_{x\in B_d}(-1)^{x\cdot y},\qquad \hat\mu(0)=1,\quad|\hat\mu|\le1 .
--   $$
--
--   The proof of the transition estimate expresses $p_\ell$ and $\Pr[W_\tau=e_{n+1}]$ through $\hat\mu$ and bounds them with moment and tail estimates for $\hat\mu$.
--
--   **Formalization Note** `chi`, `fhat`, `avgY`, `probY`, `muHat n d = fhat (mu n d)`.
-- source:
--   M. Saglam, Linear codes exceeding the Gilbert–Varshamov bound, STOC 2027 submission manuscript (held version, sha256 ac6f2bba913aa15cfec8dda07a8e9e37b7186e145fef4719cb623dd04d15baa3), §3.1, p.3 (⟨f,g⟩, χ_y, f̂); Lemma 3.1, p.4 (µ̂, E_y, Pr_y)

import Mathlib
import Definitions.Def_SaglamGV_Code
import Definitions.Def_SaglamGV_Walk

namespace SaglamGV

/-- The character `χ_y(x) = (−1)^{x·y}` (M. Saglam, *Linear codes exceeding the Gilbert–Varshamov
bound*, STOC 2027 submission manuscript (held version, sha256 ac6f2bba…), §3.1, p.3). -/
def chi {n : ℕ} (y x : Fin n → ZMod 2) : ℝ := if dot x y = 0 then 1 else -1

/-- The (unnormalized) Fourier transform `f̂(y) = ⟨f, χ_y⟩ = ∑_x f(x) χ_y(x)` (Saglam, §3.1, p.3:
"We define the Fourier transform of a function as the coefficients in this character basis:
f̂(y) = ⟨f, χ_y⟩"; "Note our Fourier transform is 2^{n/2} times a unitary").

**Formalization Note** No normalizing factor: `f̂(0) = ∑_x f(x)`. -/
noncomputable def fhat {n : ℕ} (f : (Fin n → ZMod 2) → ℝ) (y : Fin n → ZMod 2) : ℝ :=
  ∑ x, f x * chi y x

/-- `E_y g(y)`, the average over `y` uniform on `𝔽₂ⁿ` (Saglam, §3.1, p.3, `E_y`). -/
noncomputable def avgY {n : ℕ} (g : (Fin n → ZMod 2) → ℝ) : ℝ := (∑ y, g y) / (2 : ℝ) ^ n

open Classical in
/-- `Pr_y[P(y)]` for `y` uniform on `𝔽₂ⁿ` (Saglam, Lemma 3.1, p.4, `Pr_y`). -/
noncomputable def probY {n : ℕ} (P : (Fin n → ZMod 2) → Prop) : ℝ :=
  avgY (fun y => if P y then (1 : ℝ) else 0)

/-- `μ̂`, the Fourier transform of `μ = 1_{B_d}/V`: `μ̂(y) = (1/V) ∑_{x ∈ B_d} (−1)^{x·y}`
(Saglam, Lemma 3.1, p.4 and §3.3, p.4). -/
noncomputable def muHat (n d : ℕ) : (Fin n → ZMod 2) → ℝ := fhat (mu n d)

end SaglamGV


