-- Prove2me | Definitions.Def_CountingLLL_DetCount_CSP
-- name    : CountingLLL_DetCount_CSP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:46:33.780347+00:00
-- url     : https://prove2.me/theorems/09972e59-9bea-4ade-a423-59afe143801c
-- title:
--   CSP formulas, the uniform product measure, $Z(\mathcal E)$, $r_{\mathcal C,c_0}$ and the parameters $q,k,D,p$
-- statement:
--   A **CSP formula** $\Phi=(V,\mathcal Q,\mathcal C)$ has variables $V=\{0,\dots,n-1\}$; variable $v$ has the finite domain $Q_v=\{0,\dots,q_v-1\}$ with $q_v\ge 2$. Constraints are indexed by $\{0,\dots,m-1\}$; constraint $c$ has a nonempty scope $\mathrm{vbl}(c)\subseteq V$ and a Boolean function $c:\prod_{v\in\mathrm{vbl}(c)}Q_v\to\{\mathrm{True},\mathrm{False}\}$. A configuration $\sigma\in\mathcal Q=\prod_v Q_v$ satisfies $c$ when $c(\sigma_{\mathrm{vbl}(c)})=\mathrm{True}$.
--
--   $\mathbb P$ is the uniform product measure on $\mathcal Q$, written as the counting ratio $\mathbb P[A]=|\{\sigma: A(\sigma)\}|/|\mathcal Q|$, and $\mathbb P[A\mid B]=\mathbb P[A\wedge B]/\mathbb P[B]$. For a family $\mathcal E$ of constraints, $Z(\mathcal E)$ is the number of configurations satisfying every constraint of $\mathcal E$ (so $Z(\emptyset)=|\mathcal Q|$), and $Z_\Phi=Z(\mathcal C)$. The constraint marginal of equation (7) is
--   $$r_{\mathcal E,c_0}=1-\frac{Z(\mathcal E)}{Z(\mathcal E\setminus\{c_0\})}.$$
--
--   The parameters are the domain size $q=\max_v|Q_v|$, the width $k=\max_c|\mathrm{vbl}(c)|$, the dependency degree $D=\max_{c}|\{c'\ne c:\mathrm{vbl}(c)\cap\mathrm{vbl}(c')\ne\emptyset\}|$ (defined also for any subfamily $\mathcal E$, counting only neighbours in $\mathcal E$), and the violation probability $p=\max_c\mathbb P[\neg c]$. The **standing assumption** is $q\ge2$, $k\ge2$, $D\ge1$, and **Condition 1.1** is
--   $$4\mathrm e\,p\,(D+1)^2\le 1.$$
--
--   These objects are the common vocabulary of every statement of the mission.
--
--   **Formalization Note** Constraints are indexed, so duplicate constraints are allowed. Maxima over an empty index set are $0$; the standing assumption excludes those cases for the goal.
-- source:
--   Hongyang Liu, Chunyang Wang, Yitong Yin, Yiyao Zhang, Can Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 submission #442 (October 2026), §1.1 (model, parameters, Condition 1.1), §2.1, equation (7), PDF p. 3 (printed p. 2); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Mathlib

set_option autoImplicit false

namespace CountingLLL.DetCount

/-- A CSP formula `Φ = (V, Q, C)` in the sense of §1.1 and §2.1 of Liu–Wang–Yin–Zhang–Zhou.
Variables are `Fin n`; variable `v` has the finite domain `Fin (q v)` with `q v ≥ 2`;
constraints are indexed by `Fin m`; constraint `c` has a nonempty scope `scope c ⊆ V` and a
Boolean predicate `pred c` on assignments to its scope (`true` means satisfied).
Duplicate constraints (equal scopes and predicates at different indices) are allowed. -/
structure CSP where
  n : ℕ
  m : ℕ
  q : Fin n → ℕ
  two_le_q : ∀ v, 2 ≤ q v
  scope : Fin m → Finset (Fin n)
  scope_nonempty : ∀ c, (scope c).Nonempty
  pred : (c : Fin m) → ((v : ↥(scope c)) → Fin (q v.1)) → Bool

namespace CSP

variable (Φ : CSP)

/-- The configuration space `Q = ∏_v Q_v`. -/
abbrev Config : Type := (v : Fin Φ.n) → Fin (Φ.q v)

/-- `σ` satisfies constraint `c`: the predicate is `true` on the restriction `σ|vbl(c)`. -/
def Sat (c : Fin Φ.m) (σ : Φ.Config) : Prop :=
  Φ.pred c (fun v => σ v.1) = true

/-- `σ` satisfies every constraint of the subfamily `E` (the event `E` of §2.1). -/
def SatAll (E : Finset (Fin Φ.m)) (σ : Φ.Config) : Prop :=
  ∀ c ∈ E, Φ.Sat c σ

/-- `σ` violates every constraint of `T` (the event `⋀_{c ∈ T} ¬c`). -/
def ViolAll (T : Finset (Fin Φ.m)) (σ : Φ.Config) : Prop :=
  ∀ c ∈ T, ¬ Φ.Sat c σ

/-- Probability of an event under the uniform product measure `P` on `Q`, as a counting ratio
`|{σ ∈ Q : A σ}| / |Q|` (`|Q| ≥ 1` since every domain is nonempty). -/
noncomputable def prob (A : Φ.Config → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter A).card : ℝ) / (Fintype.card Φ.Config : ℝ)

/-- Conditional probability `P[A | B] = P[A ∧ B] / P[B]`. Every conditioning event used in the
paper has positive probability (by the local lemma); Lean's `x / 0 = 0` is never relied on in a
statement. -/
noncomputable def condProb (A B : Φ.Config → Prop) : ℝ :=
  Φ.prob (fun σ => A σ ∧ B σ) / Φ.prob B

/-- `Z(E)`: the number of configurations satisfying every constraint of `E`. `Z(∅) = |Q|`. -/
noncomputable def Z (E : Finset (Fin Φ.m)) : ℕ := by
  classical
  exact (Finset.univ.filter (Φ.SatAll E)).card

/-- The partition function `Z_Φ = Z(C)`: the number of satisfying assignments. -/
noncomputable def ZPhi : ℕ := Φ.Z Finset.univ

/-- The constraint marginal `r_{E,c₀} = 1 − Z(E) / Z(E ∖ {c₀})` of equation (7), for a
subfamily `E` and `c₀ ∈ E`. -/
noncomputable def r (E : Finset (Fin Φ.m)) (c₀ : Fin Φ.m) : ℝ :=
  1 - (Φ.Z E : ℝ) / (Φ.Z (E.erase c₀) : ℝ)

/-- Two constraints share a variable. -/
def Overlap (c c' : Fin Φ.m) : Prop :=
  ¬ Disjoint (Φ.scope c) (Φ.scope c')

/-- The neighbours of `c` inside the subfamily `E`: `{c' ∈ E ∖ {c} : vbl(c) ∩ vbl(c') ≠ ∅}`. -/
noncomputable def nbr (E : Finset (Fin Φ.m)) (c : Fin Φ.m) : Finset (Fin Φ.m) := by
  classical
  exact E.filter (fun c' => c' ≠ c ∧ Φ.Overlap c c')

/-- Domain size `q = max_v |Q_v|`. -/
def qmax : ℕ := Finset.univ.sup Φ.q

/-- Width `k = max_c |vbl(c)|`. -/
def kmax : ℕ := Finset.univ.sup (fun c => (Φ.scope c).card)

/-- Dependency degree of a subfamily `E`: `max_{c ∈ E} |{c' ∈ E ∖ {c} : vbl(c) ∩ vbl(c') ≠ ∅}|`
(`0` for the empty family). -/
noncomputable def Dsub (E : Finset (Fin Φ.m)) : ℕ := E.sup (fun c => (Φ.nbr E c).card)

/-- Dependency degree `D` of the formula (the whole constraint set). -/
noncomputable def Dmax : ℕ := Φ.Dsub Finset.univ

/-- Violation probability `P[¬c]` as a nonnegative real. -/
noncomputable def violProb (c : Fin Φ.m) : NNReal := by
  classical
  exact ((Finset.univ.filter (fun σ => ¬ Φ.Sat c σ)).card : NNReal) /
    (Fintype.card Φ.Config : NNReal)

/-- Violation probability `p = max_c P[¬c]`. -/
noncomputable def pmax : ℝ := ((Finset.univ.sup Φ.violProb : NNReal) : ℝ)

/-- The standing assumption of §1.1: `q ≥ 2`, `k ≥ 2` and `D ≥ 1`. (Every `|Q_v| ≥ 2` is part
of the structure `CSP`.) -/
def Standing : Prop := 2 ≤ Φ.qmax ∧ 2 ≤ Φ.kmax ∧ 1 ≤ Φ.Dmax

/-- Condition 1.1 (Counting and Sampling LLL condition): `4e·p·(D+1)² ≤ 1`. -/
def Condition11 : Prop :=
  4 * Real.exp 1 * Φ.pmax * ((Φ.Dmax : ℝ) + 1) ^ 2 ≤ 1

end CSP

end CountingLLL.DetCount


