-- Prove2me | Definitions.Def_AC02Frege_lift
-- name    : AC02Frege_lift
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:47:41.485092+00:00
-- url     : https://prove2.me/theorems/fa595303-9ec1-4c66-aa04-c7b4dca6ea1b
-- title:
--   The majority polynomial $h_i=\mathrm{Maj}_\ell(x_i)$, the lifted CNF $G=F\circ\mathrm{Maj}_\ell$ and its encoding length
-- statement:
--   Let $\ell$ be odd and $m=(\ell-1)/2$. On $\{0,1\}^\ell$, $H_0$ is the set of inputs with at most $m$ ones and $H_1$ the set of inputs with at least $m+1$ ones; $\mathrm{Maj}_\ell$ is $0$ on $H_0$ and $1$ on $H_1$. Its multilinear $\mathbb F_2$ polynomial is the sum of the point indicators of $H_1$:
--   $$
--   \mathrm{Maj}_\ell(x)=\sum_{S\subseteq[\ell],\ |S|\ge m+1}\ \prod_{a\in S}x_a\prod_{a\notin S}(1+x_a).
--   $$
--
--   For a CNF $F(y_1,\dots,y_n)$, each variable $y_i$ is given a block $x_i=(x_{i,1},\dots,x_{i,\ell})$ of new variables, $N=n\ell$ in all, and $h_i(x)=\mathrm{Maj}_\ell(x_i)$. The **lifted CNF** $G=F\circ\mathrm{Maj}_\ell$ replaces each positive literal $y_i$ by the CNF $\bigwedge_{|A|=m+1}\bigvee_{a\in A}x_{i,a}$ of $\mathrm{Maj}_\ell(x_i)$, each negative literal by $\bigwedge_{|A|=m+1}\bigvee_{a\in A}\neg x_{i,a}$, and distributes each clause into CNF: a clause $J$ of $F$ yields, for every choice of an $(m+1)$-subset $A_\lambda\subseteq[\ell]$ for each literal $\lambda=(i,s)\in J$, the clause $\bigcup_{\lambda\in J}\{(x_{i,a})^{s}:a\in A_\lambda\}$.
--
--   The **encoding length** $|G|$ is the number of literal occurrences of $G$ plus one per clause.
--
--   **Formalization Note** Block positions are `Fin ℓ`, lifted variables `Fin n × Fin ℓ`, and $m$ is `ℓ / 2`. The paper fixes no particular encoding of $G$; the count used is polynomially related to any standard one.
-- source:
--   Alekseev, Gryaznov, Pitassi, Robere, Shekhovtsov, Tzameret, Progress on AC0[2]-Frege Lower Bounds (manuscript dated November 3, 2026, STOC 2027 submission, sha256 88d149fa2bcae702e55a6b72efecda2b4137fd18dca3e23a056c3db5da0ece61), Definition 1.2, p.4; Definitions 4.1–4.2, pp.19–20; §1.1, p.4

import Mathlib
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_AC02Frege_ML

namespace AC02Frege

open MvPolynomial LiftSAParity

/-- The **majority polynomial** of one block of `ℓ` variables (Definition 4.1, p.19): the
multilinear `𝔽₂` polynomial of `Maj_ℓ`, which is zero on `H₀` (inputs with at most
`m = (ℓ-1)/2` ones) and one on `H₁` (inputs with at least `m + 1` ones). It is written as the sum,
over the points `S ⊆ [ℓ]` of `H₁`, of the point indicators `∏_{a ∈ S} x_a ∏_{a ∉ S} (1 + x_a)`.

**Formalization Note** For odd `ℓ`, `m = ℓ / 2` (natural division), so `H₁ = {S : ℓ / 2 < |S|}`.
Each point indicator contains every variable exactly once, so the polynomial is multilinear as
written. Block variables are `Fin ℓ` (the paper's `a ∈ [ℓ]`, shifted to start at `0`). -/
noncomputable def majOne (ℓ : ℕ) : MvPolynomial (Fin ℓ) (ZMod 2) :=
  ∑ S ∈ (Finset.univ : Finset (Finset (Fin ℓ))).filter (fun S => ℓ / 2 < S.card),
    ∏ a : Fin ℓ, (if a ∈ S then X a else 1 + X a)

/-- The lifted variable `h_i(x) = Maj_ℓ(x_{i,1}, …, x_{i,ℓ})` of block `i` (Definition 4.2, p.19),
as a polynomial in the `N = nℓ` lifted variables `x_{i,a}`, `(i, a) ∈ Fin n × Fin ℓ`. -/
noncomputable def hBlock {n ℓ : ℕ} (i : Fin n) : MvPolynomial (Fin n × Fin ℓ) (ZMod 2) :=
  rename (fun a : Fin ℓ => (i, a)) (majOne ℓ)

/-- The clauses of `F ∘ Maj_ℓ` produced by one clause `J` of `F` (Definition 4.2, pp.19–20): each
positive literal `y_i` is replaced by the CNF `⋀_{|A|=m+1} ⋁_{a ∈ A} x_{i,a}` of `Maj_ℓ(x_i)`, each
negative literal by `⋀_{|A|=m+1} ⋁_{a ∈ A} ¬x_{i,a}`, and the clause is distributed into CNF. So
for every choice of an `(m+1)`-subset `A_λ ⊆ [ℓ]` for each literal `λ = (i, s) ∈ J` there is the
clause `⋃_{λ ∈ J} {((i, a), s) : a ∈ A_λ}` (the polarity `s` is kept). -/
def liftClause {n : ℕ} (ℓ : ℕ) (J : Clause (Fin n)) : Finset (Clause (Fin n × Fin ℓ)) :=
  (J.pi (fun _ => (Finset.univ : Finset (Fin ℓ)).powersetCard (ℓ / 2 + 1))).image
    (fun A => J.attach.biUnion
      (fun l => (A l.1 l.2).image (fun a : Fin ℓ => ((l.1.1, a), l.1.2))))

/-- The **majority-lifted CNF** `G = F ∘ Maj_ℓ` over the `N = nℓ` variables `x_{i,a}`
(Definition 1.2, p.4; Definition 4.2, pp.19–20). -/
def lift {n : ℕ} (F : CNF (Fin n)) (ℓ : ℕ) : CNF (Fin n × Fin ℓ) :=
  F.biUnion (liftClause ℓ)

/-- The **encoding length** `|G|` of a CNF (§1.1, p.4): the number of literal occurrences plus
one separator per clause.

**Formalization Note** The paper does not fix an encoding; any standard one is polynomially
related to this count once variable names of `O(log N)` bits are accounted for, which is
immaterial for "polynomial size". -/
def encLength {V : Type*} (G : CNF V) : ℕ :=
  ∑ C ∈ G, (C.card + 1)

end AC02Frege


