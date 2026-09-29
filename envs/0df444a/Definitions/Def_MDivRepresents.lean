-- Prove2me | Definitions.Def_MDivRepresents
-- name    : MDivRepresents
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/b5ea3d12-6ae8-5271-ad20-0f7dda3e1905
-- title:
--   Incidence data representing m-division on the level-Nq curve
-- statement:
--   Standing context: a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a level $N\neq 0$, a field $k$ of characteristic $q$ with a ring homomorphism $red : A \to k$, and data `data`, `hKr`, `hα`, `hβ` describing a modular polynomial with its Kronecker congruence and the integrality of the two Hecke degeneracy maps. Two abbreviations name elements of the geometric level-$Nq$ function field `modularFunctionFieldBar (N * q)`: `jNFun` is the $q$-expansion $j(Nz)$ and `jNQFun` is $j(Nqz)$, each placed in that field by base change of coefficients to $\overline{\mathbb Q}$; alongside them sit `ProlongationTuple.jFun` ($j$) and `ProlongationTuple.jQFun` ($j(qz)$). `evalBar N q c H` evaluates a polynomial $H$ in the three variables indexed by `Option (Fin 2)` with coefficients in $A$ at an assignment $c$ of those variables by elements of the level-$Nq$ field, the coefficients being mapped along $A \hookrightarrow \overline{\mathbb Q} \to F$. The predicates `IsFstTriple v c z y₁ y₂` and `IsSndTriple v c z y₁ y₂`, for a place $v$ of the level-$N$ function field over $k$ and $c \in k$, each assert a disjunction of two normalisations: for `IsFstTriple` either $(z,y_1,y_2)=(j,\,j_N,\,j_{Nq})$ together with $\mathrm{ord}_v(\mathtt{jGeomGen}\,k\,N - c)=1$, or $(z,y_1,y_2)=(j_N,\,j,\,j_{Nq})$ together with $\mathrm{ord}_v(\mathtt{jNGeomGen}\,k\,N - c)=1$; for `IsSndTriple` the triples are $(j_q,\,j_{Nq},\,j)$ and $(j_{Nq},\,j_q,\,j)$ with the same two uniformiser conditions. Thus the relevant generator downstairs, shifted by $c$, is required to be a uniformiser at $v$.
--
--   `MDivRepresents` is a predicate on: a place specialisation $P$; tuples $Q_1 : \mathrm{Fin}\,d_1 \to$ places of the level-$Nq$ geometric field, $Q_2 : \mathrm{Fin}\,d_2 \to$ such places, and a second pair $Q_1', Q_2'$ of the same shapes; a natural number $m'$; a family $h$ of $(d_1+d_2)m'+1$ elements of that field; and incidence data $D$ of type [`IncidenceSystem.Data (d₁ + d₂) 2 m' A`](../def/IncidenceSystem.html#L18). It is the conjunction of two clauses. First, for every index $i$ of $\mathrm{Fin}(d_1+d_2)$ there exist $z, y_1, y_2$ in the level-$Nq$ field and $\tau \in A$ such that, splitting $i$ through $\mathrm{Fin}\,d_1 \oplus \mathrm{Fin}\,d_2$: the triple satisfies `IsFstTriple` at `P.reduceFst (Q₁ i₁)` with $c = red(D.u₀\,i)$ in the left case, and `IsSndTriple` at `P.reduceSnd (Q₂ i₂)` in the right case; both polynomials $G_{i,0}, G_{i,1}$ of $D$ vanish at $(z,y_1,y_2)$ and the variable `some 1` does not occur in $G_{i,0}$; at the $i$-th place of the concatenation of $Q_1$ and $Q_2$ one has $\mathrm{ord}(z - D.u₀\,i) > 0$ and $\mathrm{ord}(y_j - D.w₀\,i\,j\,0) > 0$ for $j = 0,1$, while at the $i$-th place of the concatenation of $Q_1'$ and $Q_2'$ one has $\mathrm{ord}(z - \tau) > 0$; for every $kk$ in `Option (Fin ((d₁ + d₂) * m'))` the identity
--   $$p_{kk,i}(z,y_1,y_2) = c_{kk}\,(z - D.u₀\,i)^{m'}(z-\tau)\,s_{kk,i}(z,y_1,y_2)$$
--   holds, with $c_{kk} = 1$ for $kk = \mathrm{none}$ and $c_{kk} = h(k.\mathrm{succ})$ for $kk = \mathrm{some}\,k$; the $\mathrm{none}$ component is pinned exactly, $D.p\,\mathrm{none}\,i = (X_{\mathrm{none}} - u^0_i)^{m'}(X_{\mathrm{none}} - \tau)$, $D.s\,\mathrm{none}\,i = 1$ and $D.\sigma_0\,\mathrm{none}\,i =$ the jet supported at index $0$ with value $1$; and finally the reductions $red(D.sVal\,D.centre\,kk\,i)$ and $red(D.dG\,D.centre\,i\,j)$ are all non-zero, i.e. the values of the $s_{kk,i}$ and the partial derivatives $\partial_{y_j} G_{i,j}$ at the centre of $D$ are units of $A$. Second, for every variable $v$ of the incidence system [`IncidenceSystem.Var (d₁ + d₂) 2 m'`](../def/IncidenceSystem.html#L9), the value of the system polynomial $D.\mathrm{system}\,v$ at $D.\mathrm{centre}$ lies in the maximal ideal of $A$, so that the centre is a root of the system modulo $\mathfrak m_A$. The definition asserts nothing by itself; it records the compatibility between analytic data on the level-$Nq$ curve and the purely polynomial incidence data over $A$.
--
--   **Relation to Mathlib.** Mathlib supplies the ambient `MvPolynomial`, `ValuationSubring`, Laurent series and `IsLocalRing.maximalIdeal` machinery; the incidence data [`IncidenceSystem.Data`](../def/IncidenceSystem.html#L18), the geometric modular function fields and the place-specialisation apparatus are the project's own.
--
--   **Where it is used.** The predicate is the interface between a place specialisation of the modular curve of level $Nq$ at $q$ and an auxiliary system of polynomial equations over the valuation ring $A$: it records that the chosen triples of modular functions at the marked places satisfy the incidence relations, with unit partial derivatives and unit denominators at the centre, and that the centre solves the system modulo the maximal ideal. It is the hypothesis under which divisibility statements in the Jacobian at level $Nq$ are reduced to solving the incidence system over the residue field, within the analysis at $q$ of $J_0(Nq)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_MDivRepresents.lean

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_IncidenceSystem

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

namespace ModularCurve.PlaceSpecialization

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

noncomputable abbrev jNFun (N q : ℕ) [NeZero N] [NeZero q] : modularFunctionFieldBar (N * q) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (N * q) (dvd_mul_right N q))⟩

noncomputable abbrev jNQFun (N q : ℕ) [NeZero N] [NeZero q] : modularFunctionFieldBar (N * q) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (N * q) jq),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (N * q) (dvd_refl (N * q)))⟩

noncomputable def evalBar (N q : ℕ) (c : Option (Fin 2) → modularFunctionFieldBar (N * q))
    (H : MvPolynomial (Option (Fin 2)) A) : modularFunctionFieldBar (N * q) :=
  MvPolynomial.eval₂ ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).comp
    (algebraMap A (AlgebraicClosure ℚ))) c H

def IsFstTriple (v : Place k (modularFunctionFieldC k N)) (c : k) (z y₁ y₂ : modularFunctionFieldBar (N * q)) :
    Prop :=
  (z = ProlongationTuple.jFun N q ∧ y₁ = jNFun N q ∧ y₂ = jNQFun N q ∧
      v.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) c) = 1) ∨
    (z = jNFun N q ∧ y₁ = ProlongationTuple.jFun N q ∧ y₂ = jNQFun N q ∧
      v.ord (jNGeomGen k N - algebraMap k (modularFunctionFieldC k N) c) = 1)

def IsSndTriple (v : Place k (modularFunctionFieldC k N)) (c : k) (z y₁ y₂ : modularFunctionFieldBar (N * q)) :
    Prop :=
  (z = ProlongationTuple.jQFun N q ∧ y₁ = jNQFun N q ∧ y₂ = ProlongationTuple.jFun N q ∧
      v.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) c) = 1) ∨
    (z = jNQFun N q ∧ y₁ = ProlongationTuple.jQFun N q ∧ y₂ = ProlongationTuple.jFun N q ∧
      v.ord (jNGeomGen k N - algebraMap k (modularFunctionFieldC k N) c) = 1)

def MDivRepresents (P : PlaceSpecialization A q N data hKr k red hα hβ)
    {d₁ d₂ : ℕ}
    (Q₁ : Fin d₁ → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (Q₂ : Fin d₂ → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (Q₁' : Fin d₁ → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (Q₂' : Fin d₂ → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (m' : ℕ) (h : Fin ((d₁ + d₂) * m' + 1) → modularFunctionFieldBar (N * q))
    (D : IncidenceSystem.Data (d₁ + d₂) 2 m' A) : Prop :=
  (∀ i : Fin (d₁ + d₂),
    ∃ (z y₁ y₂ : modularFunctionFieldBar (N * q)) (τ : A),

      Sum.elim (fun i₁ => IsFstTriple (q := q) (P.reduceFst (Q₁ i₁)) (red (D.u₀ i)) z y₁ y₂)
          (fun i₂ => IsSndTriple (q := q) (P.reduceSnd (Q₂ i₂)) (red (D.u₀ i)) z y₁ y₂) (finSumFinEquiv.symm i) ∧

      (∀ j : Fin 2, evalBar N q (fun o => Option.elim o z ![y₁, y₂]) (D.G i j) = 0) ∧
      (some 1 : Option (Fin 2)) ∉ (D.G i 0).vars ∧

      0 < (Sum.elim Q₁ Q₂ (finSumFinEquiv.symm i)).ord
            (z - algebraMap (AlgebraicClosure ℚ) _ (D.u₀ i : AlgebraicClosure ℚ)) ∧
      (∀ j : Fin 2, 0 < (Sum.elim Q₁ Q₂ (finSumFinEquiv.symm i)).ord
            (![y₁, y₂] j - algebraMap (AlgebraicClosure ℚ) _ (D.w₀ i j 0 : AlgebraicClosure ℚ))) ∧
      0 < (Sum.elim Q₁' Q₂' (finSumFinEquiv.symm i)).ord
            (z - algebraMap (AlgebraicClosure ℚ) _ (τ : AlgebraicClosure ℚ)) ∧

      (∀ kk : Option (Fin ((d₁ + d₂) * m')),
        evalBar N q (fun o => Option.elim o z ![y₁, y₂]) (D.p kk i) =
          Option.elim kk 1 (fun kk => h kk.succ) *
            (z - algebraMap (AlgebraicClosure ℚ) _ (D.u₀ i : AlgebraicClosure ℚ)) ^ m' *
            (z - algebraMap (AlgebraicClosure ℚ) _ (τ : AlgebraicClosure ℚ)) *
            evalBar N q (fun o => Option.elim o z ![y₁, y₂]) (D.s kk i)) ∧
      D.p none i = (MvPolynomial.X none - MvPolynomial.C (D.u₀ i)) ^ m' *
        (MvPolynomial.X none - MvPolynomial.C τ) ∧
      D.s none i = 1 ∧
      D.σ₀ none i = Pi.single 0 1 ∧

      (∀ kk : Option (Fin ((d₁ + d₂) * m')), red (D.sVal D.centre kk i) ≠ 0) ∧

      (∀ j : Fin 2, red (D.dG D.centre i j) ≠ 0)) ∧

  (∀ v : IncidenceSystem.Var (d₁ + d₂) 2 m',
    MvPolynomial.eval D.centre (D.system v) ∈ IsLocalRing.maximalIdeal A)

end ModularCurve.PlaceSpecialization


