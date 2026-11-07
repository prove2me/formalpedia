-- Prove2me | Definitions.Def_AC02Frege_majorityExpansion
-- name    : AC02Frege_majorityExpansion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:48:50.953593+00:00
-- url     : https://prove2.me/theorems/81d64637-1bff-4d86-8470-19629ef4e163
-- title:
--   The majority basis: light sets $\mathcal A$, coefficient polynomials $p_A$, coefficient degree $\beta$, $W_Q$ and $\widehat C_D$
-- statement:
--   Let $\ell$ be odd, $m=(\ell-1)/2$, and work with polynomials in the lifted variables $x_{i,a}$. For $A\subseteq[n]\times[\ell]$ let $A_i=\{a:(i,a)\in A\}$, and put
--   $$
--   \mathcal A=\{A: |A_i|\le m \text{ for every } i\},
--   $$
--   the index set of the light monomials $x_A$. For a monomial $x_T$, $J(T)=\{i:|T_i|>m\}$ is its set of heavy blocks.
--
--   By Lemma 4.5 every polynomial $p$ has a unique **majority expansion**
--   $$
--   p(x)=\sum_{A\in\mathcal A}x_A\,p_A\bigl(h_1(x),\dots,h_n(x)\bigr)
--   $$
--   with multilinear **coefficient polynomials** $p_A(y_1,\dots,y_n)$. The **coefficient degree** is $\beta(p)=\max_{A\in\mathcal A}\deg_y p_A$, with $\beta(0)=-\infty$, and $W_Q=\{p:\beta(p)\le Q\}$. The **lifted consequence space** is
--   $$
--   \widehat C_D=\{p(x):\ p_A(y)\in C_D \text{ for every } A\in\mathcal A\},
--   $$
--   with $C_D$ the degree-$D$ PC consequence space of $F$ in the original variables; it is not claimed to be the consequence space of $G$. Finally, the number of blocks on which $v$ depends is the number of blocks $i$ some variable $x_{i,a}$ of which occurs in the multilinear polynomial of $v$.
--
--   **Formalization Note** The expansion is multilinearized, the family $(p_A)$ is indexed by all subsets with $p_A=0$ off $\mathcal A$, and `coeffPoly p` is the unique such family when it exists and is unique (Lemma 4.5) and $0$ otherwise. $\beta$ takes values in `WithBot ℕ`.
-- source:
--   Alekseev, Gryaznov, Pitassi, Robere, Shekhovtsov, Tzameret, Progress on AC0[2]-Frege Lower Bounds (manuscript dated November 3, 2026, STOC 2027 submission, sha256 88d149fa2bcae702e55a6b72efecda2b4137fd18dca3e23a056c3db5da0ece61), Definitions 4.4, 4.6, 4.7, 4.9 and (17), (18), pp.21–22; Lemma 4.10, p.23

import Mathlib
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_AC02Frege_ML
import Definitions.Def_AC02Frege_PC
import Definitions.Def_AC02Frege_lift

namespace AC02Frege

open MvPolynomial LiftSAParity

/-- The part `A_i = {a : (i, a) ∈ A}` of a set `A ⊆ [n] × [ℓ]` of lifted variables in block `i`
(Definition 4.4, p.21), kept as a set of lifted variables. -/
def blockPart {n ℓ : ℕ} (A : Finset (Fin n × Fin ℓ)) (i : Fin n) : Finset (Fin n × Fin ℓ) :=
  A.filter (fun v => v.1 = i)

/-- The index set `𝒜 = {A ⊆ [n] × [ℓ] : |A_i| ≤ m for every i}` of light monomials `x_A`, which
select at most half the bits of every block (Definition 4.4, p.21; `m = ℓ / 2` for odd `ℓ`). -/
def lightSets (n ℓ : ℕ) : Finset (Finset (Fin n × Fin ℓ)) :=
  Finset.univ.filter (fun A => ∀ i : Fin n, (blockPart A i).card ≤ ℓ / 2)

/-- The set `J(T) = {i : |T_i| > m}` of heavy blocks of a monomial `x_T` (Definition 4.7, p.22). -/
def heavyBlocks {n ℓ : ℕ} (T : Finset (Fin n × Fin ℓ)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => ℓ / 2 < (blockPart T i).card)

/-- The majority expansion of a family of coefficient polynomials
(Lemma 4.5, (17), p.21): `Σ_{A ∈ 𝒜} x_A · q_A(h_1(x), …, h_n(x))`, multilinearized. -/
noncomputable def expand {n ℓ : ℕ} (q : Finset (Fin n × Fin ℓ) → MvPolynomial (Fin n) (ZMod 2)) :
    MvPolynomial (Fin n × Fin ℓ) (ZMod 2) :=
  ML (∑ A ∈ lightSets n ℓ, xMon A * bind₁ (fun i => hBlock (ℓ := ℓ) i) (q A))

/-- `q` is a majority expansion of (the function of) `p` (Lemma 4.5, (17), p.21): every `q_A` is a
multilinear polynomial in the original variables `y_1, …, y_n`, `q_A = 0` for `A ∉ 𝒜`, and
`ML(p) = Σ_{A ∈ 𝒜} x_A q_A(h)`. -/
def IsExpansion {n ℓ : ℕ} (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2))
    (q : Finset (Fin n × Fin ℓ) → MvPolynomial (Fin n) (ZMod 2)) : Prop :=
  (∀ A, IsMultilinear (q A)) ∧ (∀ A ∉ lightSets n ℓ, q A = 0) ∧ expand q = ML p

/-- The **coefficient polynomials** `p_A(y)` of `p` (Definition 4.6, p.21): the unique majority
expansion of Lemma 4.5.

**Formalization Note** Defined as the unique `q` with `IsExpansion p q` when it exists and is
unique (Lemma 4.5 says it always is, for odd `ℓ`), and `0` otherwise. A polynomial is identified
with its function, i.e. with `ML p`. -/
noncomputable def coeffPoly {n ℓ : ℕ} (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :
    Finset (Fin n × Fin ℓ) → MvPolynomial (Fin n) (ZMod 2) :=
  open Classical in
  if h : ∃! q, IsExpansion p q then h.choose else 0

/-- The **coefficient degree** `β(p) = max_{A ∈ 𝒜} deg_y p_A` (Definition 4.6, p.21), with
`β(0) = −∞`.

**Formalization Note** Valued in `WithBot ℕ`; a zero coefficient polynomial contributes `⊥`, so
`β(p) = ⊥` exactly when every coefficient polynomial vanishes. -/
noncomputable def coeffDeg {n ℓ : ℕ} (p : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) : WithBot ℕ :=
  (lightSets n ℓ).sup (fun A =>
    if coeffPoly p A = 0 then ⊥ else ((coeffPoly p A).totalDegree : WithBot ℕ))

/-- `W_Q = {p : β(p) ≤ Q}` (Definition 4.6, p.21). -/
def WQ (n ℓ Q : ℕ) : Set (MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :=
  {p | coeffDeg p ≤ (Q : WithBot ℕ)}

/-- The **lifted consequence space** `Ĉ_D = {p(x) : p_A(y) ∈ C_D for every A ∈ 𝒜}`
(Definition 4.9, (18), p.22), with `C_D` the degree-`D` PC consequence space of `F` in the
original variables. It is not claimed to be the consequence space of `F ∘ Maj_ℓ`. -/
def CHat {n : ℕ} (F : CNF (Fin n)) (ℓ D : ℕ) : Set (MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) :=
  {p | ∀ A ∈ lightSets n ℓ, coeffPoly p A ∈ CD F D}

/-- The number of blocks on which (the function of) `v` depends (Lemma 4.10, p.23): the blocks
`i` some variable `x_{i,a}` of which occurs in the multilinear polynomial `ML v`. -/
noncomputable def blocksOf {n ℓ : ℕ} (v : MvPolynomial (Fin n × Fin ℓ) (ZMod 2)) : ℕ :=
  ((ML v).vars.image Prod.fst).card

end AC02Frege


