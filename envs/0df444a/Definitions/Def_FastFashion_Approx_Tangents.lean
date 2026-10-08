-- Prove2me | Definitions.Def_FastFashion_Approx_Tangents
-- name    : FastFashion_Approx_Tangents
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T01:14:09.513691+00:00
-- url     : https://prove2.me/theorems/5a7442a2-a6ff-492c-8112-07e3a7485157
-- title:
--   §3.1.3: lower incomplete Gamma $\gamma$, tangent coefficients $a_k, b_i$ of (6) (index corrected), and the approximation $\tilde g_\lambda$ of (8)
-- statement:
--   This file defines the deterministic approximation of expected sales of Caro and Gallien (§3.1.3).
--
--   The **lower incomplete Gamma function** is, for an integer $a \ge 1$ and real $b$,
--   $$\gamma(a, b) = \int_0^b v^{a-1} e^{-v}\,dv.$$
--
--   For a rate $\lambda > 0$ and a period $T > 0$, the **tangent slopes and intercepts** are
--   $$a_k(\lambda) = \frac{\gamma(k+1, \lambda T)}{\lambda\, \Gamma(k+1)} = \frac{\gamma(k+1,\lambda T)}{\lambda\, k!}, \qquad b_i(\lambda) = \sum_{k=0}^{i-1} a_k(\lambda), \quad b_0(\lambda) = 0,$$
--   for $k, i \in \mathbb N$. The **discrete tangent** with index $i \in \mathbb N \cup \{\infty\}$ is the affine function
--   $$x \mapsto a_i(\lambda)(x - i) + b_i(\lambda) \quad (i \in \mathbb N), \qquad x \mapsto T \quad (i = \infty),$$
--   the latter being the paper's extension $a_\infty(\lambda) = 0$, $b_\infty(\lambda) = T$.
--
--   Given major sizes $\mathcal S^+ \ne \emptyset$, minor sizes $\mathcal S^- = \mathcal S \setminus \mathcal S^+$, rates $\lambda = (\lambda_s)$, and for every size a nonempty finite set $\mathcal N(\lambda_s) \subseteq \mathbb N \cup \{\infty\}$ of tangent indices, the **approximate expected sales function** of (8) is
--   $$\tilde g_\lambda(q) = \lambda_{\mathcal S^+} \min_{s \in \mathcal S^+} \min_{i \in \mathcal N(\lambda_s)} \{a_i(\lambda_s)(q_s - i) + b_i(\lambda_s)\} + \sum_{s \in \mathcal S^-} \lambda_s \min_{s' \in \mathcal S^+ \cup \{s\}} \min_{i \in \mathcal N(\lambda_{s'})} \{a_i(\lambda_{s'})(q_{s'} - i) + b_i(\lambda_{s'})\},$$
--   where $\lambda_{\mathcal S^+} = \sum_{s \in \mathcal S^+} \lambda_s$ and $q \in \mathbb N^{\mathcal S}$.
--
--   It is a linear combination of minima of affine functions of $q$, which is what lets the paper embed it in a mixed integer program.
--
--   **Formalization Note** *Corrected index.* The paper prints $a_k(\lambda_s) = \gamma(k, \lambda_s T)/(\lambda_s \Gamma(k))$ and $b_i = \sum_{k=0}^{i-1} a_k$; as printed, $b_1 = a_0$ involves $\Gamma(0)$, which is undefined, and the slopes are shifted by one against (5). The paper's own description of $a_k$ ("the probability that the $(k+1)$-th unit of size $s$ will sell before the next replenishment", weighted by the mean inter-arrival time) fixes the reading used here: $a_k$ is the $(k+1)$-th term of the sum (5), so $b_i = \mathbb E[\tau_s(i) \wedge T]$. *Domain.* $\gamma(a,\cdot)$ is defined with a natural-number exponent $a-1$; every use has $a \ge 1$, so the truncated subtraction never applies. *Index sets.* The paper's rule (7), "$b_i(\lambda_s) \approx 0, 0.3T, \dots$", is not a definition; $\mathcal N(\lambda_s)$ is an arbitrary nonempty finite set. The nonemptiness of $\mathcal S^+$ and of each $\mathcal N(\lambda_s)$ are arguments of $\tilde g$, needed for the minima to exist. $q_s - i$ is a real subtraction.
-- source:
--   Caro & Gallien, Inventory Management of a Fast-Fashion Retail Network, working paper (August 2, 2007), p. 12, Eqs. (5)–(7) (γ, a_k, b_i; a_k index corrected); p. 13, Eq. (8)

import Mathlib

namespace FastFashion.Approx

/-- The lower incomplete Gamma function `γ(a, b) = ∫_0^b v^{a-1} e^{-v} dv` (p. 12), for integer
order `a ≥ 1` (every use in the paper has `a ≥ 1`). -/
noncomputable def lowerGamma (a : ℕ) (b : ℝ) : ℝ :=
  ∫ v in (0 : ℝ)..b, v ^ (a - 1) * Real.exp (-v)

/-- The tangent slope `a_k(λ) = γ(k+1, λT) / (λ Γ(k+1)) = γ(k+1, λT) / (λ k!)`, the paper's `a_k`
of (6) with the index shifted by one (Eq. (6), p. 12, corrected): it is the `(k+1)`-th term of the
sum (5). -/
noncomputable def a (lam T : ℝ) (k : ℕ) : ℝ :=
  lowerGamma (k + 1) (lam * T) / (lam * (Nat.factorial k : ℝ))

/-- The tangent intercept `b_i(λ) = ∑_{k=0}^{i-1} a_k(λ)`, with `b_0(λ) = 0` (Eq. (6), p. 12). -/
noncomputable def b (lam T : ℝ) (i : ℕ) : ℝ :=
  ∑ k ∈ Finset.range i, a lam T k

/-- The discrete tangent with index `i ∈ ℕ ∪ {∞}` evaluated at `x`: `a_i(λ)(x − i) + b_i(λ)` for
finite `i`, and the constant `T` for `i = ∞` (the paper's extension `a_∞ = 0`, `b_∞ = T`). -/
noncomputable def tangent (lam T : ℝ) : WithTop ℕ → ℝ → ℝ
  | ⊤, _ => T
  | (n : ℕ), x => a lam T n * (x - (n : ℝ)) + b lam T n

/-- The lower envelope `min_{i ∈ 𝒩} {a_i(λ)(x − i) + b_i(λ)}` of the tangents indexed by a
nonempty finite set `𝒩 ⊆ ℕ ∪ {∞}`. -/
noncomputable def envelope (lam T : ℝ) (Nf : Finset (WithTop ℕ)) (hNf : Nf.Nonempty) (x : ℝ) : ℝ :=
  Nf.inf' hNf (fun i => tangent lam T i x)

/-- `min_{s ∈ D} min_{i ∈ 𝒩(λ_s)} {a_i(λ_s)(q_s − i) + b_i(λ_s)}` for a nonempty set of sizes `D`. -/
noncomputable def sizeMin {S : Type*} (lam : S → ℝ) (T : ℝ) (Nset : S → Finset (WithTop ℕ))
    (hN : ∀ s, (Nset s).Nonempty) (D : Finset S) (hD : D.Nonempty) (q : S → ℕ) : ℝ :=
  D.inf' hD (fun s => envelope (lam s) T (Nset s) (hN s) (q s : ℝ))

/-- The approximation `g̃_λ(q)` of Eq. (8) (p. 13):
`λ_{S⁺} min_{s ∈ S⁺} min_{i ∈ 𝒩(λ_s)} {…} + ∑_{s ∈ S⁻} λ_s min_{s' ∈ S⁺ ∪ {s}} min_{i ∈ 𝒩(λ_{s'})} {…}`,
with `λ_{S⁺} = ∑_{s ∈ S⁺} λ_s` and `S⁻ = Spᶜ`. -/
noncomputable def gTilde {S : Type*} [Fintype S] [DecidableEq S] (lam : S → ℝ) (T : ℝ)
    (Sp : Finset S) (hSp : Sp.Nonempty) (Nset : S → Finset (WithTop ℕ))
    (hN : ∀ s, (Nset s).Nonempty) (q : S → ℕ) : ℝ :=
  (∑ s ∈ Sp, lam s) * sizeMin lam T Nset hN Sp hSp q +
    ∑ s ∈ Spᶜ, lam s * sizeMin lam T Nset hN (insert s Sp) (Finset.insert_nonempty s Sp) q

end FastFashion.Approx


