-- Prove2me | Definitions.Def_SetMultCost_relrk
-- name    : SetMultCost_relrk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:52:59.365138+00:00
-- url     : https://prove2.me/theorems/0367a46e-cb79-4bf8-84ed-ee6529ff5393
-- title:
--   Relative rank $\mathrm{relrk}_{n,\alpha,\pi}$
-- statement:
--   Fix a partition $\pi=(\mathcal P,\mathcal N)$ of $[d]$ and a real $\alpha\in(0,1]$. The variable parts have $|X^{(i)}|=\lfloor n^\alpha\rfloor$ for $i\in\mathcal P$ and $|X^{(i)}|=n$ for $i\in\mathcal N$. For a polynomial $Q$, let $M_{n,\alpha,\pi}(Q)$ be its **coefficient matrix**: rows are the set-multilinear monomials on $\mathcal P$, columns those on $\mathcal N$, and the $(m_1,m_2)$ entry is the coefficient of $m_1m_2$ in $Q$. With $d_{\mathcal P}=|\mathcal P|$, $d_{\mathcal N}=|\mathcal N|$, $R=\lfloor n^\alpha\rfloor^{d_{\mathcal P}}$ and $C=n^{d_{\mathcal N}}$, the **relative rank** is
--
--   $$\mathrm{relrk}_{n,\alpha,\pi}(Q)=\frac{\mathrm{rank}_F\,M_{n,\alpha,\pi}(Q)}{\sqrt{RC}}.$$
--
--   It is the complexity measure of the mission: small on the low-depth circuits, large on a projection of $\mathrm{IMM}_{n,d}$.
--
--   **Formalization Note** A factor of a product lives only on a subset $T$ of the parts, so the definition takes $T$, with rows on $T\cap\mathcal P$ and columns on $T\setminus\mathcal P$; the paper's measure is $T=[d]$. `relrkAB` allows arbitrary sizes $A,B$ in place of $\lfloor n^\alpha\rfloor, n$. The power $n^\alpha$ is real, so $R\ne n^{\alpha d_{\mathcal P}}$ in general, which is why Lemma 2.2(3) has a factor $2$.
-- source:
--   Behera, Forbes, Saptharishi, Tavenas, On the Cost of Set-Multilinearisation in Positive Characteristic, STOC 2027 submission (manuscript sha256 841308db…), §2, p.8; Definition 2.1, pp.8–9

import Mathlib

namespace SetMultCost

/-- The variables of a set-multilinear family on `d` parts: `⟨i, a⟩` is the `a`-th variable of the
part `X⁽ⁱ⁾`, which has `sz i` variables. The part of a variable is `Sigma.fst`. -/
abbrev Var (d : ℕ) (sz : Fin d → ℕ) := Σ i : Fin d, Fin (sz i)

/-- Part sizes for a partition `π = (P, N)`, with `N` the complement of `P`: `A` on `P`, `B` on `N`.
The paper's family (p.8) has `A = ⌊n^α⌋`, `B = n`. -/
def sizeFn {d : ℕ} (P : Finset (Fin d)) (A B : ℕ) : Fin d → ℕ := fun i => if i ∈ P then A else B

/-- The monomial that takes the variable `x i` from each part `i ∈ U`. -/
noncomputable def partialMonomial {d : ℕ} {sz : Fin d → ℕ} (U : Finset (Fin d))
    (x : (i : U) → Fin (sz i)) : Var d sz →₀ ℕ :=
  ∑ i : U, Finsupp.single ⟨i.1, x i⟩ 1

/-- **The coefficient matrix** `M_{n,α,π}(Q)` (p.8): "For a row index m1 and a column index m2, the
entry of the (m1, m2)th matrix is the coefficient of the monomial m1m2 in the polynomial P."

**Formalization Note.** A factor of a product lives only on a subset `T` of the parts (Lemma 2.2(2),
with its partition `πᵢ`), so rows are the monomials on `T ∩ P` and columns those on `T \ P`. The
paper's matrix is the case `T = Finset.univ`. -/
noncomputable def coeffMatrix {F : Type*} [CommRing F] {d : ℕ} {sz : Fin d → ℕ}
    (P T : Finset (Fin d)) (Q : MvPolynomial (Var d sz) F) :
    Matrix ((i : ↥(T ∩ P)) → Fin (sz i.1)) ((i : ↥(T \ P)) → Fin (sz i.1)) F :=
  Matrix.of fun m₁ m₂ => MvPolynomial.coeff (partialMonomial _ m₁ + partialMonomial _ m₂) Q

/-- The relative rank with part sizes `A` on `P` and `B` on `N`:
`rank M / √(A^{|T ∩ P|} · B^{|T \ P|})`. The denominator is `√(RC)`, for `R` the number of rows
and `C` the number of columns. Corollary 2.7's proof uses it for sizes `m^β` and `m`. -/
noncomputable def relrkAB {F : Type*} [Field F] {d : ℕ} (A B : ℕ) (P T : Finset (Fin d))
    (Q : MvPolynomial (Var d (sizeFn P A B)) F) : ℝ :=
  ((coeffMatrix P T Q).rank : ℝ) / √((A : ℝ) ^ (T ∩ P).card * (B : ℝ) ^ (T \ P).card)

/-- **Relative rank.** Behera, Forbes, Saptharishi, Tavenas, *On the Cost of Set-Multilinearisation in Positive
Characteristic*, STOC 2027 submission (manuscript sha256 841308db…), Definition 2.1, pp.8–9: "relrkn,α,π(P) := rankF(Mn,α,π(P)) / √(RC),
where the rank is over the field F", with `|X⁽ⁱ⁾| = ⌊n^α⌋` for `i ∈ P` and `n` for `i ∈ N`, and
`R = ⌊n^α⌋^{d_P}`, `C = n^{d_N}`.

**Formalization Note.** `n^α` is the real power, so `R` differs from `n^{α d_P}` when `n^α` is not an
integer; this is why Lemma 2.2(3) has a factor `2`. `T` is the set of parts the polynomial lives on,
so `d_P = |T ∩ P|` and `d_N = |T \ P|`, and the paper's measure is `T = Finset.univ`. `n = 0` gives
a zero denominator, so a zero value; every statement excludes it. -/
noncomputable def relrk {F : Type*} [Field F] {d : ℕ} (n : ℕ) (α : ℝ) (P T : Finset (Fin d))
    (Q : MvPolynomial (Var d (sizeFn P ⌊(n : ℝ) ^ α⌋₊ n)) F) : ℝ :=
  relrkAB ⌊(n : ℝ) ^ α⌋₊ n P T Q

end SetMultCost


