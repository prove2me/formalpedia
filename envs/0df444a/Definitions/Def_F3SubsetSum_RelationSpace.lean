-- Prove2me | Definitions.Def_F3SubsetSum_RelationSpace
-- name    : F3SubsetSum_RelationSpace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:29:53.646208+00:00
-- url     : https://prove2.me/theorems/95089a9f-8711-4be5-be19-808508d0bf65
-- title:
--   The relation space $N$ of the quotient decoder (eqs. (30)–(38))
-- statement:
--   Fix $q\ge3$ prime, an instance $(A,b)$, an integer $D\ge2$, and for every reduced degree-$D$ monomial $x^\alpha$ elements $Q_{i,\alpha}\in R_{D-2}$ with
--
--   $$
--   \sum_{i=1}^m L_i^2Q_{i,\alpha}=x^\alpha\ \text{ in }R_D. \tag{30}
--   $$
--
--   Let $V=\langle\mathcal M_{<D}\rangle\subseteq S$ be the span of the reduced monomials of degree below $D$, and let $\mathrm{red}(\cdot)$ reduce modulo $I=(x_j^q-x_j)_j$ by replacing $x_j^q$ by $x_j$. Define
--
--   $$
--   r_\alpha=x^\alpha-\mathrm{red}\Bigl(\sum_i f_iQ_{i,\alpha}\Bigr),\qquad
--   \tau(x^\alpha)=\begin{cases}x^\alpha,&|\alpha|<D,\\ r_\alpha,&|\alpha|=D,\end{cases}\qquad
--   \mathsf X_j(v)=\tau(\mathrm{red}(x_jv)),
--   $$
--
--   $\mathsf L_i=\sum_j(a_i)_j\mathsf X_j$, $\mathsf F_i=(\mathsf L_i-b_i\mathsf I)(\mathsf L_i-b_i\mathsf I+\mathsf I)$, $\mathsf C_{j,k}=\mathsf X_j\mathsf X_k-\mathsf X_k\mathsf X_j$, $\mathsf H_j=\mathsf X_j^q-\mathsf X_j$, and
--
--   $$
--   N_0=\sum_{j<k}\mathsf C_{j,k}(V)+\sum_j\mathsf H_j(V)+\sum_i\mathsf F_i(V),\qquad N_{r+1}=N_r+\sum_j\mathsf X_j(N_r).
--   $$
--
--   The **relation space** $N$ is the stable value of this increasing chain. It is what the decoder computes; Proposition 4.9 identifies $V/N$ with $S/J$.
--
--   **Formalization Note** $Q_{i,\alpha}$ is lifted to $S$ by its reduced representative. $\tau$ sends monomials outside its domain (never produced) to $0$. The images $\mathsf C_{j,k}(V)$ etc. enter through their spans, and $N=\bigcup_r N_r$ (the supremum of the chain).
-- source:
--   Kothari, Metger, O'Donnell, Shutty, Wu, Exponential quantum speedup for F_3^n-Subset-Sum? Or, rigorous classical algorithms for Binary-Error LWE, arXiv:2609.40321v1, §4.2, eqs. (30)–(38), pp.19–20

import Mathlib
import Definitions.Def_F3SubsetSum_QuotientAlgebra
import Definitions.Def_F3SubsetSum_TruncatedRing

namespace F3SubsetSum

open MvPolynomial

/-! The objects of §4.2 (Kothari, Metger, O'Donnell, Shutty, Wu, arXiv:2609.40321v1,
pp.19–21), for an instance `(A, b) ∈ F_q^{n×m} × F_q^m`, a degree `D ≥ 2`, and a family
`Q_{i,α} ∈ R_{D−2}` satisfying (30). Throughout, `S = F_q[x_1, …, x_n]`. -/

section
variable {q n m : ℕ}

/-- **The space `V = ⟨ℳ_{<D}⟩`** (p.19): the span in `S` of the reduced monomials of degree
below `D`, `ℳ_{<D} = {x^α : α ∈ {0, …, q − 1}ⁿ, |α| < D}`. -/
noncomputable def lowSpan (q n D : ℕ) : Submodule (ZMod q) (MvPolynomial (Fin n) (ZMod q)) :=
  Submodule.span (ZMod q)
    {p | ∃ s : Fin n →₀ ℕ, (∀ j, s j < q) ∧ ∑ j, s j < D ∧ p = monomial s 1}

/-- The exponent of `x_j` after reducing `x_j^e` modulo `x_j^q − x_j`: `e` if `e < q`, else the
unique `e' ∈ {1, …, q − 1}` with `e' ≡ e (mod q − 1)`. -/
def redExp (q e : ℕ) : ℕ := if e < q then e else (e - 1) % (q - 1) + 1

/-- **The reduction `red(·)`** (p.19): "red(·) computes the remainder modulo I by repeatedly
replacing x_j^q by x_j", `I = (x_1^q − x_1, …, x_n^q − x_n)`. It maps every monomial `x^s` to the
reduced monomial with exponents `redExp q (s j)`, and extends linearly. -/
noncomputable def red (q : ℕ) (p : MvPolynomial (Fin n) (ZMod q)) : MvPolynomial (Fin n) (ZMod q) :=
  ∑ s ∈ p.support, monomial (Finsupp.equivFunOnFinite.symm fun j => redExp q (s j)) (coeff s p)

variable (A : Matrix (Fin n) (Fin m) (ZMod q)) (b : Fin m → ZMod q) (D : ℕ)
  (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))

/-- **The remainder `r_α`** of eq. (31), p.19: `r_α = x^α − red(Σ_i f_i Q_{i,α})`, for the
reduced degree-`D` monomial `x^α`, where `Q_{i,α} ∈ R_{D−2}` is lifted to `S` by its reduced
representative. -/
noncomputable def remainder (α : ReducedMono n q D) : MvPolynomial (Fin n) (ZMod q) :=
  monomial α.toFinsupp 1 - red q (∑ i, fPoly A b i * Rd.toPoly (ZMod q) n q (D - 2) (Q α i))

/-- **The map `τ`** of eq. (32), p.19: on reduced polynomials of degree at most `D`, it fixes
every monomial `x^α` with `|α| < D` and replaces every reduced degree-`D` monomial by `r_α`
(extended linearly). Monomials outside this domain (never produced below) are sent to `0`. -/
noncomputable def tau (p : MvPolynomial (Fin n) (ZMod q)) : MvPolynomial (Fin n) (ZMod q) :=
  ∑ s ∈ p.support,
    if ∑ j, s j < D then monomial s (coeff s p)
    else if h : (∀ j, s j < q) ∧ ∑ j, s j = D then
      coeff s p • remainder A b D Q ⟨fun j => ⟨s j, h.1 j⟩, h.2⟩
    else 0

/-- **The multiplication maps** `X_j(v) = τ(red(x_j v))`, eq. (33), p.20. -/
noncomputable def Xop (j : Fin n) (v : MvPolynomial (Fin n) (ZMod q)) :
    MvPolynomial (Fin n) (ZMod q) :=
  tau A b D Q (red q (X j * v))

/-- `L_i(v) = (Σ_j (a_i)_j X_j)(v)`, eq. (34), p.20. -/
noncomputable def Lop (i : Fin m) (v : MvPolynomial (Fin n) (ZMod q)) :
    MvPolynomial (Fin n) (ZMod q) :=
  ∑ j, A j i • Xop A b D Q j v

/-- **The sample relations** `F_i(v) = ((L_i − b_i·I)(L_i − b_i·I + I))(v)`, eq. (34), p.20. -/
noncomputable def Fop (i : Fin m) (v : MvPolynomial (Fin n) (ZMod q)) :
    MvPolynomial (Fin n) (ZMod q) :=
  let w := Lop A b D Q i v - b i • v + v
  Lop A b D Q i w - b i • w

/-- **The commutator relations** `C_{j,k}(v) = (X_j X_k − X_k X_j)(v)`, eq. (35), p.20. -/
noncomputable def Cop (j k : Fin n) (v : MvPolynomial (Fin n) (ZMod q)) :
    MvPolynomial (Fin n) (ZMod q) :=
  Xop A b D Q j (Xop A b D Q k v) - Xop A b D Q k (Xop A b D Q j v)

/-- **The field-equation relations** `H_j(v) = (X_j^q − X_j)(v)`, eq. (36), p.20. -/
noncomputable def Hop (j : Fin n) (v : MvPolynomial (Fin n) (ZMod q)) :
    MvPolynomial (Fin n) (ZMod q) :=
  (Xop A b D Q j)^[q] v - Xop A b D Q j v

/-- **`N_0`**, eq. (37), p.20:
`N_0 = Σ_{1≤j<k≤n} C_{j,k}(V) + Σ_j H_j(V) + Σ_i F_i(V)`, as the span of these images. -/
noncomputable def relN0 : Submodule (ZMod q) (MvPolynomial (Fin n) (ZMod q)) :=
  Submodule.span (ZMod q)
    ({w | ∃ j k : Fin n, j < k ∧ ∃ v ∈ lowSpan q n D, w = Cop A b D Q j k v} ∪
      {w | ∃ j : Fin n, ∃ v ∈ lowSpan q n D, w = Hop A b D Q j v} ∪
      {w | ∃ i : Fin m, ∃ v ∈ lowSpan q n D, w = Fop A b D Q i v})

/-- **`N_r`**, eq. (38), p.20: `N_{r+1} = N_r + Σ_j X_j(N_r)`. -/
noncomputable def relNr : ℕ → Submodule (ZMod q) (MvPolynomial (Fin n) (ZMod q))
  | 0 => relN0 A b D Q
  | r + 1 => relNr r ⊔ Submodule.span (ZMod q)
      {w | ∃ j : Fin n, ∃ v ∈ relNr r, w = Xop A b D Q j v}

/-- **The relation space `N`** (p.20): "Stop when N_{r+1} = N_r and call the resulting space N."
The chain `N_0 ⊆ N_1 ⊆ ⋯` is increasing, so its stable value is its union `⨆_r N_r`. -/
noncomputable def relSpace : Submodule (ZMod q) (MvPolynomial (Fin n) (ZMod q)) :=
  ⨆ r, relNr A b D Q r

end

end F3SubsetSum


