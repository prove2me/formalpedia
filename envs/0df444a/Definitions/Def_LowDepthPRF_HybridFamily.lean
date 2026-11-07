-- Prove2me | Definitions.Def_LowDepthPRF_HybridFamily
-- name    : LowDepthPRF_HybridFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:38:57.307445+00:00
-- url     : https://prove2.me/theorems/0d508954-7ca8-46a6-82b9-7ba9bae6a4b7
-- title:
--   Definition 4.8 and Figure 3: the hybrid families $\mathscr F'_{(m',j)}$
-- statement:
--   For $j\in\{0,\dots,c_q\}$, the family $\mathscr F_{(j)}$ is $\mathscr F_\lambda$ with TGGM replaced by $\mathrm{TGGM}_{(j)}$ (Figure 3). The state at level $j+1$ is
--
--   $$y^{(j+1)}=R(\tilde x_1\dots\tilde x_j)\in\{0,1\}^{\lambda^{(j+1)}},$$
--
--   for a uniformly random function $R:[\Delta]^j\to\{0,1\}^{\lambda^{(j+1)}}$ that is part of the key. The levels $j+1,\dots,\ell$ are then computed as in TGGM. For $m'\in[m]$, the hybrid family (Definition 4.8) is
--
--   $$\mathscr F'_{(m',j)}=\mathscr F_{(c_q)}^{\oplus(m'-1)}\oplus\mathscr F_{(j)}\oplus\mathscr F_{(0)}^{\oplus(m-m')}.$$
--
--   Hybrid $\mathbf H_{1,m',j}$ gives oracle access to a random member of $\mathscr F'_{(m',j)}$.
--
--   These families carry the two-stage hybrid argument of Theorem 4.6. Lemma 4.9 handles the computational steps $j\to j+1$, and Lemma 4.10 the final statistical step.
--
--   **Formalization Note** For $j=0$, the paper sets $y^{(1)}=k_G$. Here $R$ on the single empty prefix plays the role of $k_G$, as in the paper's proof of Lemma 4.10. A uniform such $R$ is a uniform $k_G$, so the games are the same. Prefixes longer than $\ell$ are padded and never used.
-- source:
--   Ding, Jain, Komargodski, Pseudorandom Functions in NC¹ from LWE/LPN/CDH, arXiv:2608.25213 (sha256 89a55849…), Definition 4.8, p.19 (pdf 21); Figure 3, p.20 (pdf 22)

import Mathlib
import Definitions.Def_LowDepthPRF_TaperingGGM

namespace LowDepthPRF

/-!
# Definition 4.8 and Figure 3: the hybrid families `ℱ′_{(m′,j)}`

Ding, Jain, Komargodski, *Pseudorandom Functions in NC¹ from LWE/LPN/CDH*, arXiv:2608.25213
(sha256 89a55849…), Definition 4.8, p.19, and Figure 3 (Hybrid TGGM_{(j)}), p.20.

**Formalization Note.**
* `ℱ_{(j)}` is `ℱ_λ` with TGGM replaced by TGGM_{(j)}: the state `y^{(j+1)}` (length
  `λ^{(j+1)} = tl λ j`) is `R(x̃_1 … x̃_j)` for a uniformly random function
  `R : [Δ]^j → {0,1}^{λ^{(j+1)}}` that is part of the key, and the levels `j+1, …, ℓ` are as in
  TGGM. The key is `(R, k_XG, k_H)`.
* For `j = 0`, Figure 3 sets `y^{(1)} ← k_G`. Here `R` on the single (empty) prefix plays the
  role of `k_G` (the paper's proof of Lemma 4.10 reads `R` on the empty prefix as the uniform root
  key the same way); a uniform `R : [Δ]^0 → {0,1}^λ` is a uniform `k_G`, so `ℱ_{(0)}` and `ℱ_λ`
  define the same games.
* The prefix of `x̃` of length `j` is defined for every `j`; for `j > ℓ` it is padded with `0`
  (a case never used: the hybrids have `j ≤ c_q < ℓ`).
* `ℱ′_{(m′,j)} = ℱ_{(c_q)}^{⊕(m′−1)} ⊕ ℱ_{(j)} ⊕ ℱ_{(0)}^{⊕(m−m′)}`: fold `i` (zero-based, `i < m = λ`)
  is `ℱ_{(c_q)}` if `i + 1 < m′`, `ℱ_{(j)}` if `i + 1 = m′`, and `ℱ_{(0)}` otherwise; the key is the
  tuple of fold keys and the output is the XOR (Definition 3.8). Hybrid `H_{1,m′,j}` is the
  strong real game `strongReal (hybridFam … m′ j)`.
-/

/-- `x̃_{1…j}`, the length-`j` prefix of `x̃ ∈ [Δ]^ℓ` (padded with `0` beyond `ℓ`). -/
noncomputable def prefixOf {lam : ℕ} (xt : Fin (ell lam) → Fin (Delta lam)) (j : ℕ) : Fin j → Fin (Delta lam) :=
  fun i => if h : (i : ℕ) < ell lam then xt ⟨i, h⟩ else ⟨0, Nat.two_pow_pos _⟩

/-- A key `(R, k_XG, k_H)` of `ℱ_{(j)}`. -/
abbrev HybKey (p : ℕ → ℕ) (kh : ℕ → ℕ) (lam j : ℕ) : Type :=
  ((Fin j → Fin (Delta lam)) → Fin (tl lam j) → Bool) × Pool p lam × (Fin (kh lam) → Bool)

/-- `ℱ_{(j)}` (Figure 3): `y^{(j+1)} = R(x̃_{1…j})`, then levels `j+1, …, ℓ` of TGGM. -/
noncomputable def hybTree {p : ℕ → ℕ} (G : (n : ℕ) → FunFam (Fin n → Bool) (p n) (ceilSqrt n))
    {kh : ℕ → ℕ} (H : (lam : ℕ) → FunFam (Fin (kh lam) → Bool) lam (ell lam * logDelta lam))
    (lam j : ℕ) : FunFam (HybKey p kh lam j) lam (tl lam (ell lam)) :=
  fun key x =>
    let xt : Fin (ell lam) → Fin (Delta lam) := fun k => blockIdx (H lam key.2.2 x) k
    runTo (ell lam) (levelStep G key.2.1 xt) j (key.1 (prefixOf xt j))

/-- The level of fold `i` of `ℱ′_{(m′,j)}`: `c_q` before fold `m′`, `j` at fold `m′`, `0` after. -/
noncomputable def foldLevel (q lam m' j : ℕ) (i : Fin lam) : ℕ :=
  if (i : ℕ) + 1 < m' then cq q lam else if (i : ℕ) + 1 = m' then j else 0

/-- Definition 4.8: `ℱ′_{(m′,j)} = ℱ_{(c_q)}^{⊕(m′−1)} ⊕ ℱ_{(j)} ⊕ ℱ_{(0)}^{⊕(m−m′)}` (`m = λ`). -/
noncomputable def hybridFam {p : ℕ → ℕ} (G : (n : ℕ) → FunFam (Fin n → Bool) (p n) (ceilSqrt n))
    {kh : ℕ → ℕ} (H : (lam : ℕ) → FunFam (Fin (kh lam) → Bool) lam (ell lam * logDelta lam))
    (q lam m' j : ℕ) :
    FunFam ((i : Fin lam) → HybKey p kh lam (foldLevel q lam m' j i)) lam (tl lam (ell lam)) :=
  sumFam (K := fun i => HybKey p kh lam (foldLevel q lam m' j i))
    (fun i => hybTree G H lam (foldLevel q lam m' j i))

end LowDepthPRF


