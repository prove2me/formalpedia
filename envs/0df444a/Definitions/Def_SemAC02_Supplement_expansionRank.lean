-- Prove2me | Definitions.Def_SemAC02_Supplement_expansionRank
-- name    : SemAC02_Supplement_expansionRank
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T19:43:40.399718+00:00
-- url     : https://prove2.me/theorems/6fe4fe85-1057-486d-84be-9433daa59c34
-- title:
--   Boundary expanders and the expansion pseudo-reduction operator (Definition 5.2)
-- statement:
--   For a bipartite graph $G=(L\sqcup R,E)$, the boundary $\partial_G(J)$ of $J\subseteq L$ is the set of right vertices with exactly one neighbour in $J$; $G$ is an **$(s,c)$-boundary expander** if $|\partial_G(J)|\ge c|J|$ whenever $|J|\le s$.
--
--   A **clustered representation** writes a polynomial system as $F=F_0\cup\bigcup_{u\in L}F_u$ with background axioms $F_0$, left axiom clusters $F_u$ and right variable clusters $V_v$ ($v\in R$) partitioning the variables; $u$ and $v$ are adjacent when some polynomial of $F_u$ mentions a variable of $V_v$. It is **respectful** if, whenever $v$ has a unique neighbour $u$ in some $J\subseteq L$, an assignment to $V_v$ sets every polynomial of $F_u$ to zero and sets to zero or leaves unchanged each background axiom.
--
--   Fix a degree-compatible monomial order. A monomial is **irreducible** modulo an ideal $I$ of $B$ if it is not the leading monomial of an element of $I$, and $R_I(p)$ is the combination of irreducible monomials congruent to $p$. With $\mathrm{Sup}_s(A)=\bigcup\{J\subseteq L:|J|\le s,\ \partial_G(J)\subseteq A\}$, $N(t)$ the clusters met by a monomial $t$ and $I(J)=\langle F_0\cup\bigcup_{u\in J}F_u\rangle$, the **expansion operator** is
--
--   $$
--   R(t)=R_{I(\mathrm{Sup}_s(N(t)))}(t)
--   $$
--
--   on standard monomials (irreducible modulo $\langle F_0\rangle$) of degree at most $K$, extended linearly.
--
--   Theorem 5.4 bounds the rank of this operator.
--
--   **Formalization Note** The boundary is the published `PCNonBool.boundaryOn`. Elements of $B$ are multilinear polynomials; the normal form is chosen by `Classical.choose` (it is unique). `expRank` is the dimension of the span of the values $R(t)$ on standard monomials of degree at most $k$, which is $\operatorname{rank}(R_{\le k})$.
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), §5.1, pp.37–39 (PDF pp.39–41), Definition 5.2, p.39 (PDF p.41)

import Mathlib
import Definitions.Def_AC02Frege_ML
import Definitions.Def_SemAC02_Ble
import Definitions.Def_PCNonBool_BipGraph
import Definitions.Def_PCNonBool_boundaryOn

namespace SemAC02.Supplement

open MvPolynomial

/-- An **`(s, c)`-boundary expander** (Alekseev–Gryaznov–Itsykson–Pitassi–Robere–Tzameret, *Hard
Instances for Strong Semantic Proof Systems*, manuscript (STOC 2027 submission), §5.1, p.37): a
bipartite graph `G = (L ⊔ R, E)` with `|∂_G(J)| ≥ c|J|` for every `J ⊆ L` with `|J| ≤ s`, where
`∂_G(J) = {v ∈ R : |N_G(v) ∩ J| = 1}` is the published `PCNonBool.boundaryOn G univ J`.

**Formalization Note** `s` and `c` are real numbers (no degree bound is bundled). -/
def IsBdryExp {L R : Type} [Fintype R] (G : PCNonBool.BipGraph L R) (s c : ℝ) : Prop :=
  ∀ J : Finset L, (J.card : ℝ) ≤ s →
    c * (J.card : ℝ) ≤ ((PCNonBool.boundaryOn G Finset.univ J).card : ℝ)

/-- A **clustered representation** of a polynomial system (§5.1, p.38):
`F = F₀ ∪ ⋃_{u ∈ L} F_u`, with background axioms `F₀`, left axiom clusters `F_u` (`u ∈ L`), and
right variable clusters `V_v = {x : cluster x = v}` (`v ∈ R`) partitioning the variables. -/
structure ClusteredRep (σ L R : Type) where
  /-- the background axioms `F₀` -/
  F0 : Set (MvPolynomial σ (ZMod 2))
  /-- the left axiom clusters `F_u` -/
  Fu : L → Set (MvPolynomial σ (ZMod 2))
  /-- the right cluster `v` of each variable -/
  cluster : σ → R

namespace ClusteredRep

variable {σ L R : Type}

/-- All axioms `F₀ ∪ ⋃_{u ∈ L} F_u`. -/
def axioms (P : ClusteredRep σ L R) : Set (MvPolynomial σ (ZMod 2)) :=
  P.F0 ∪ {p | ∃ u, p ∈ P.Fu u}

/-- The graph of the representation (p.38): "join `u` and `v` whenever a polynomial in `F_u`
contains a variable from `V_v`". -/
noncomputable def graph [DecidableEq σ] (P : ClusteredRep σ L R) : PCNonBool.BipGraph L R :=
  open Classical in
  { Adj := fun u v => ∃ p ∈ P.Fu u, ∃ x ∈ p.vars, P.cluster x = v }

/-- Partial substitution of the values `α` for the variables of the cluster `V_v`. -/
noncomputable def substCluster (P : ClusteredRep σ L R) (v : R) (α : σ → ZMod 2)
    (p : MvPolynomial σ (ZMod 2)) : MvPolynomial σ (ZMod 2) :=
  open Classical in aeval (fun x => if P.cluster x = v then C (α x) else X x) p

/-- The representation is **respectful** (p.38): for every `J ⊆ L` and every `v ∈ R` with a unique
neighbour `u` in `J`, some assignment to `V_v` sets every polynomial of `F_u` to zero and sets to
zero or leaves unchanged each background axiom (equalities in `B`, i.e. on the Boolean cube). -/
def IsRespectful [DecidableEq σ] [Fintype L] [DecidableEq L] (P : ClusteredRep σ L R) : Prop :=
  ∀ (J : Finset L) (v : R) (u : L),
    J.filter (fun u' => P.graph.Adj u' v) = {u} →
    ∃ α : σ → ZMod 2,
      (∀ p ∈ P.Fu u, ∀ y : σ → Bool, eval (toF2 y) (P.substCluster v α p) = 0) ∧
      ∀ g ∈ P.F0, (∀ y : σ → Bool, eval (toF2 y) (P.substCluster v α g) = 0) ∨
        (∀ y : σ → Bool, eval (toF2 y) (P.substCluster v α g) = eval (toF2 y) g)

end ClusteredRep

/-- The ideal `⟨G⟩` of the Boolean ring `B = 𝔽₂[x]/⟨x_i² − x_i⟩` (p.38), as the set of its elements
written as multilinear polynomials: the multilinear polynomials in the ideal of `𝔽₂[x]` generated
by `G` and the Boolean axioms. -/
def idealB {σ : Type} (G : Set (MvPolynomial σ (ZMod 2))) : Set (MvPolynomial σ (ZMod 2)) :=
  {q | AC02Frege.IsMultilinear q ∧
    q ∈ Ideal.span (G ∪ {p | ∃ i : σ, p = X i ^ 2 - X i})}

/-- The multilinear monomial `x_t` is **irreducible modulo `⟨G⟩`** for the monomial order `m`
(p.38): it is not the leading monomial of a (non-zero) element of the ideal. -/
def IsIrred {σ : Type} (m : MonomialOrder σ) (G : Set (MvPolynomial σ (ZMod 2)))
    (t : Finset σ) : Prop :=
  ∀ q ∈ idealB G, q ≠ 0 → m.degree q ≠ m.degree (AC02Frege.xMon t)

/-- The **normal form** `R_I(p)` modulo `I = ⟨G⟩` (p.38): the linear combination of irreducible
monomials congruent to `p` modulo `I`.

**Formalization Note** It is unique (a non-zero combination of irreducible monomials is not in
`I`); the definition picks it by choice when it exists (and is `0` otherwise, which does not
happen for a degree-compatible order). -/
noncomputable def nf {σ : Type} (m : MonomialOrder σ) (G : Set (MvPolynomial σ (ZMod 2)))
    (p : MvPolynomial σ (ZMod 2)) : MvPolynomial σ (ZMod 2) :=
  open Classical in
  if h : ∃ q ∈ Submodule.span (ZMod 2) (AC02Frege.xMon '' {t | IsIrred m G t}),
      p - q ∈ Ideal.span (G ∪ {p | ∃ i : σ, p = X i ^ 2 - X i}) then h.choose else 0

/-- The monomial order `m` is **degree-compatible**: monomials of smaller total degree are smaller. -/
def IsDegCompatible {σ : Type} (m : MonomialOrder σ) : Prop :=
  ∀ a b : σ →₀ ℕ, Finsupp.degree a < Finsupp.degree b → m.toSyn a < m.toSyn b

/-- The **`s`-support** `Sup_s(A) = ⋃ {J ⊆ L : |J| ≤ s, ∂_G(J) ⊆ A}` of `A ⊆ R` (p.38). -/
noncomputable def supS {L R : Type} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]
    (G : PCNonBool.BipGraph L R) (s : ℝ) (A : Finset R) : Finset L :=
  ((Finset.univ : Finset (Finset L)).filter
    (fun J => (J.card : ℝ) ≤ s ∧ PCNonBool.boundaryOn G Finset.univ J ⊆ A)).biUnion id

/-- The **expansion pseudo-reduction operator** on a monomial (Definition 5.2, p.39):
`R(t) = R_{I(Sup_s(t))}(t)`, where `N(t)` is the set of clusters met by `t`,
`Sup_s(t) = Sup_s(N(t))` and `I(J) = ⟨F₀ ∪ ⋃_{u∈J} F_u⟩`. -/
noncomputable def expOp {σ L R : Type} [DecidableEq σ] [Fintype L] [DecidableEq L] [Fintype R]
    [DecidableEq R] (P : ClusteredRep σ L R) (m : MonomialOrder σ) (s : ℝ) (t : Finset σ) :
    MvPolynomial σ (ZMod 2) :=
  nf m (P.F0 ∪ {p | ∃ u ∈ supS P.graph s (t.image P.cluster), p ∈ P.Fu u})
    (AC02Frege.xMon t)

/-- `rank(R_{≤k})` for the expansion operator of Definition 5.2 (p.39): `R` is defined on the
standard monomials (irreducible modulo `⟨F₀⟩`) of degree at most `K` and extended linearly to
`B_{F₀}^{≤K}`; for `k ≤ K` the image of its restriction to `B_{F₀}^{≤k}` is spanned by the
values `R(t)` on the standard monomials `t` of degree at most `k`.

**Formalization Note** The values `R(t)` are normal forms, i.e. combinations of standard
monomials, which are linearly independent in `B_{F₀}`; the rank is computed in `B`. -/
noncomputable def expRank {σ L R : Type} [DecidableEq σ] [Fintype L] [DecidableEq L] [Fintype R]
    [DecidableEq R] (P : ClusteredRep σ L R) (m : MonomialOrder σ) (s : ℝ) (k : ℕ) : ℕ :=
  Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
    (expOp P m s '' {t | IsIrred m P.F0 t ∧ t.card ≤ k}))

end SemAC02.Supplement


