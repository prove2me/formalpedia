-- Prove2me | Definitions.Def_LogBarrierIPM_Iterations_MonomialMatrix
-- name    : LogBarrierIPM_Iterations_MonomialMatrix
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T13:45:48.653978+00:00
-- url     : https://prove2.me/theorems/6aaaeaed-b9cc-45a0-88e8-081df687ef65
-- title:
--   Monomial matrices: evaluation $\mathbf M(t)$, $\operatorname{val}(\det\mathbf M)$ and the exponent gap $\eta(\mathbf M)$
-- statement:
--   A **monomial matrix** $\mathbf M$ of size $d\times d$ has entries $\epsilon_{ij}t^{\alpha_{ij}}$ with signs $\epsilon_{ij}\in\{\pm1\}$ and exponents $\alpha_{ij}\in\mathbb R\cup\{-\infty\}$, where $t^{-\infty}=0$. For a real $t>0$, $\mathbf M(t)$ is the real matrix with these entries.
--
--   Expanding the determinant over permutations,
--   $$\det\mathbf M=\sum_{\sigma\in\mathrm{Sym}_d}\operatorname{sgn}(\sigma)\prod_{i}\epsilon_{i\sigma(i)}\;t^{\sum_i\alpha_{i\sigma(i)}},$$
--   a generalized polynomial in $t$. For $\beta\in\mathbb R$, the **collected coefficient** of $t^\beta$ is the sum of $\operatorname{sgn}(\sigma)\prod_i\epsilon_{i\sigma(i)}$ over the permutations with $\sum_i\alpha_{i\sigma(i)}=\beta$. The **valuation** $\operatorname{val}(\det\mathbf M)$ is the largest $\beta$ whose collected coefficient is non-zero, and $-\infty$ if there is none (that is, if $\det\mathbf M=0$).
--
--   The **exponent gap** is
--   $$\eta(\mathbf M)=\min\Big\{\eta:\ \sigma,\tau\in\mathrm{Sym}_d,\ \eta=\sum_{i=1}^d\alpha_{i\sigma(i)}-\sum_{i=1}^d\alpha_{i\tau(i)}>0\Big\},\qquad \min\emptyset=+\infty.$$
--
--   These quantities enter the explicit comparison between $\log_t|\det\mathbf M(t)|$ and $\operatorname{val}(\det\mathbf M)$, which yields the explicit size of $t$ in the paper's main theorem.
--
--   **Formalization Note** The Puiseux field is not used: a monomial matrix is given by its exponent matrix (entries in `WithBot ℝ`) and its sign matrix (real entries, the theorem assumes each is $\pm1$). The valuation of the determinant is computed combinatorially from the permutation expansion, as above. In $\eta$ only pairs with both exponent sums finite contribute; a pair involving $-\infty$ gives no finite positive difference (the paper's formula would give $+\infty$, which does not change the minimum). $\eta$ takes values in `WithTop ℝ`.
-- source:
--   Allamigeon, Benchimol, Gaubert, Joswig, Log-Barrier Interior Point Methods Are Not Strongly Polynomial, arXiv:1708.01544v2, p. 12 (monomial matrices, η(M)), p. 13 (proof of Lemma 11: expansion of det M); p. 7 (val)

import Mathlib

namespace LogBarrierIPM.Iterations

/-- `t^a` for `a ∈ ℝ ∪ {−∞}` with the convention `t^{−∞} = 0` (p. 12). -/
noncomputable def tpow (t : ℝ) : WithBot ℝ → ℝ
  | ⊥ => 0
  | (a : ℝ) => t ^ a

/-- The real matrix `𝐌(t)` obtained by evaluating at `t > 0` the monomial matrix `𝐌 ∈ 𝕂^{d×d}`
with entries `ε_{ij} t^{α_{ij}}`, `ε_{ij} ∈ {±1}`, `α_{ij} ∈ ℝ ∪ {−∞}` (p. 12). -/
noncomputable def monoEval {d : ℕ} (α : Matrix (Fin d) (Fin d) (WithBot ℝ))
    (ε : Matrix (Fin d) (Fin d) ℝ) (t : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => ε i j * tpow t (α i j)

/-- The exponent `∑_i α_{iσ(i)} ∈ ℝ ∪ {−∞}` of the term of `det 𝐌` indexed by `σ ∈ Sym_d`. -/
def permExp {d : ℕ} (α : Matrix (Fin d) (Fin d) (WithBot ℝ)) (σ : Equiv.Perm (Fin d)) :
    WithBot ℝ :=
  ∑ i, α i (σ i)

/-- The coefficient of `t^β` in the generalized polynomial
`det 𝐌 = ∑_σ sgn(σ) ∏_i ε_{iσ(i)} t^{∑_i α_{iσ(i)}}`, collected over all `σ` whose exponent
equals `β`. -/
noncomputable def detCoeff {d : ℕ} (α : Matrix (Fin d) (Fin d) (WithBot ℝ)) (ε : Matrix (Fin d) (Fin d) ℝ)
    (β : ℝ) : ℝ :=
  ∑ σ : Equiv.Perm (Fin d),
    if permExp α σ = (β : WithBot ℝ) then
      ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, ε i (σ i) else 0

/-- `val(det 𝐌)`: the largest exponent `β ∈ ℝ` whose collected coefficient in `det 𝐌` is
non-zero, and `−∞` if there is none (i.e. `det 𝐌 = 0`) (p. 7, p. 13). -/
noncomputable def valDet {d : ℕ} (α : Matrix (Fin d) (Fin d) (WithBot ℝ))
    (ε : Matrix (Fin d) (Fin d) ℝ) : WithBot ℝ := by
  classical
  exact (Finset.univ.filter fun σ : Equiv.Perm (Fin d) =>
      ∃ β : ℝ, permExp α σ = (β : WithBot ℝ) ∧ detCoeff α ε β ≠ 0).sup (permExp α)

/-- The positive gap `∑_i α_{iσ(i)} − ∑_i α_{iτ(i)}` between the exponents of two permutations,
or `+∞` if it is not a positive real number. -/
noncomputable def expGap {d : ℕ} (α : Matrix (Fin d) (Fin d) (WithBot ℝ))
    (στ : Equiv.Perm (Fin d) × Equiv.Perm (Fin d)) : WithTop ℝ :=
  match permExp α στ.1, permExp α στ.2 with
  | (a : ℝ), (b : ℝ) => if 0 < a - b then ((a - b : ℝ) : WithTop ℝ) else ⊤
  | _, _ => ⊤

/-- `η(𝐌) = min{η : σ, τ ∈ Sym_d, η = ∑_i α_{iσ(i)} − ∑_i α_{iτ(i)} > 0}` (p. 12), with
`min ∅ = +∞`; only pairs with both exponent sums finite give a real difference. -/
noncomputable def etaM {d : ℕ} (α : Matrix (Fin d) (Fin d) (WithBot ℝ)) : WithTop ℝ :=
  Finset.univ.inf (expGap α)

end LogBarrierIPM.Iterations


