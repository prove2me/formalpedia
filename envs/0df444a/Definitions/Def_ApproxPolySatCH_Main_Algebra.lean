-- Prove2me | Definitions.Def_ApproxPolySatCH_Main_Algebra
-- name    : ApproxPolySatCH_Main_Algebra
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T16:09:47.109077+00:00
-- url     : https://prove2.me/theorems/bbe2bb08-0509-4b74-9bdb-0a3de6e09f1c
-- title:
--   Annihilators, prescribed fibers and epsilon-adic valued closures
-- statement:
--   Fix a field $k$, its algebraic closure $K$, and $L=\overline{K(\varepsilon)}$. An epsilon valuation is a map $\nu:L\to\mathbb Q\cup\{\infty\}$ with the additive valuation laws, $\nu(0)=\infty$, $\nu(c)=0$ for $c\in K^\times$, and $\nu(\varepsilon)=1$. Its axioms contain no statement about approximate satisfiability. Negative rational values are allowed.
--
--   The annihilator of a polynomial tuple is the kernel of substitution. Minimal dependence means that the full substitution is not injective and every proper subtuple substitution is injective. An annihilator presentation records its irreducible generator both before and after scalar extension. For $f=(f_1,\ldots,f_{n+1})$ and $a\in K^n$, define
--   $$V(f,a)=\{x\in L^n:f_i(x)=a_i\varepsilon\ (1\le i\le n)\}.$$
--   Localization relations are nonzero polynomials $P_j(Y,U)$ of positive $U$-degree, satisfying the exact substitution identities and the source's Perron degree bounds. Their leading coefficients define $h=\prod_jq_j$. This data does not assume finite fibers, integrality or root lifting. The Gauss valuation of a univariate polynomial is the minimum valuation of its nonzero coefficients, with value infinity on zero.
--
--   This interface supplies the mathematical objects of Claims 7–10 and Proposition 4 without restricting the original APS input.
-- source:
--   Nikhil Balaji, Mahsa Shirmohammadi, Sébastien Tavenas, James Worrell, STOC 2027 submission #1125 (October 2026), §§2,4, pp.5–8,18–20; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1125.pdf

import Definitions.Def_ApproxPolySatCH_Main_Inputs

set_option autoImplicit false

namespace ApproxPolySatCH.Main

abbrev Constants (k : Type) [Field k] := AlgebraicClosure k
abbrev ValuedClosure (k : Type) [Field k] := AlgebraicClosure (RatFunc (Constants k))

noncomputable def constantsMap (k : Type) [Field k] : Constants k →+* ValuedClosure k :=
  (algebraMap (RatFunc (Constants k)) (ValuedClosure k)).comp
    (algebraMap (Constants k) (RatFunc (Constants k)))

noncomputable def epsilon (k : Type) [Field k] : ValuedClosure k :=
  algebraMap (RatFunc (Constants k)) (ValuedClosure k) RatFunc.X

/-- An additive extension of the epsilon-adic valuation on the fixed algebraic closure.
Its complete axioms are exposed; no theorem about APS is part of this structure. -/
structure EpsilonValuation (k : Type) [Field k] where
  val : ValuedClosure k → WithTop ℚ
  zero : val 0 = ⊤
  multiply : ∀ x y, val (x * y) = val x + val y
  add : ∀ x y, min (val x) (val y) ≤ val (x + y)
  constant : ∀ c : Constants k, c ≠ 0 → val (constantsMap k c) = 0
  parameter : val (epsilon k) = 1

noncomputable def evaluateValued {k : Type} [Field k] {n : ℕ}
    (p : Poly k n) (x : Fin n → ValuedClosure k) : ValuedClosure k :=
  MvPolynomial.eval₂ ((constantsMap k).comp (algebraMap k (Constants k))) x p

noncomputable def annihilator {k : Type} [Field k] {n m : ℕ} (f : Fin m → Poly k n) :
    Ideal (Poly k m) := RingHom.ker (MvPolynomial.eval₂Hom MvPolynomial.C f)

noncomputable def extendedSystem {k : Type} [Field k] {n m : ℕ} (f : Fin m → Poly k n) :
    Fin m → Poly (Constants k) n := fun i => MvPolynomial.map (algebraMap k (Constants k)) (f i)

/-- Every proper subtuple is independent, and the whole tuple is dependent. -/
def MinimallyDependent {k : Type} [Field k] {n : ℕ} (f : Fin (n + 1) → Poly k n) : Prop :=
  ¬ Function.Injective (MvPolynomial.eval₂Hom MvPolynomial.C f) ∧
  ∀ s : Finset (Fin (n + 1)), s ≠ Finset.univ →
    Function.Injective (MvPolynomial.eval₂Hom MvPolynomial.C (fun i : s => f i.val))

noncomputable def maxDegree {k : Type} [Field k] {n m : ℕ} (f : Fin m → Poly k n) : ℕ :=
  Finset.univ.sup (fun i => (f i).totalDegree)

/-- Canonical evaluation presentations, before and after extending scalars. -/
def AnnihilatorPresentation {k : Type} [Field k] {n : ℕ}
    (f : Fin (n + 1) → Poly k n) (H : Poly k (n + 1)) : Prop :=
  Irreducible H ∧ annihilator f = Ideal.span {H} ∧
  annihilator (extendedSystem f) = Ideal.span {MvPolynomial.map (algebraMap k (Constants k)) H}

noncomputable def prescribedFiber {k : Type} [Field k] {n : ℕ}
    (f : Fin (n + 1) → Poly k n) (a : Fin n → Constants k) : Set (Fin n → ValuedClosure k) :=
  {x | ∀ i : Fin n, evaluateValued (f i.castSucc) x = constantsMap k (a i) * epsilon k}

noncomputable def specializedAnnihilator {k : Type} [Field k] {n : ℕ}
    (H : Poly k (n + 1)) (a : Fin n → Constants k) (z : ValuedClosure k) : ValuedClosure k :=
  MvPolynomial.eval₂ ((constantsMap k).comp (algebraMap k (Constants k)))
    (Fin.lastCases z (fun i => constantsMap k (a i) * epsilon k)) H

/-- The relations constructed immediately before (17), not an assumption of finite fibers. -/
structure LocalizationRelations {k : Type} [Field k] {n : ℕ}
    (f : Fin (n + 1) → Poly k n) where
  P : Fin n → Polynomial (Poly k n)
  nonzero : ∀ j, P j ≠ 0
  positiveDegree : ∀ j, 0 < (P j).natDegree
  bound : ∀ j, ((MvPolynomial.finSuccEquiv k n).symm (P j)).totalDegree ≤
    ∏ i : Fin n, (f i.castSucc).totalDegree
  relation : ∀ j, Polynomial.eval₂
    (MvPolynomial.eval₂Hom MvPolynomial.C (fun i : Fin n => f i.castSucc))
      (MvPolynomial.X j) (P j) = 0

noncomputable def localizationProduct {k : Type} [Field k] {n : ℕ}
    {f : Fin (n + 1) → Poly k n} (r : LocalizationRelations f) : Poly k n :=
  ∏ j, (r.P j).leadingCoeff

/-- A zero polynomial has infinite valuation, including when its coefficient support is empty. -/
noncomputable def gaussValuation {k : Type} [Field k] (v : EpsilonValuation k)
    (p : Polynomial (ValuedClosure k)) : WithTop ℚ := p.support.inf (fun i => v.val (p.coeff i))

end ApproxPolySatCH.Main


