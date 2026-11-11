-- Prove2me | Definitions.Def_MinimaxInterventions1429_Separable_Model
-- name    : MinimaxInterventions1429_Separable_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:52:58.41924+00:00
-- url     : https://prove2.me/theorems/81b89999-b18f-4c82-abb8-184fcae1d688
-- title:
--   Bounded separable interventions, mixtures, contrasts and quotient geometry
-- statement:
--   Let $m,k\ge2$ be the numbers of rows and actions. A payoff table is a real array $L=(L_{gh})$; the hidden table lies in $[0,1]^{m\times k}$, while perturbed tables and reconstructed outputs can be arbitrary real arrays. A mixture is a point of the closed probability simplex $\Delta_k$. Define
--
--   $$F_M(p)=\max_g\sum_h M_{gh}p_h,\qquad
--   \omega_{gh}(L)=L_{gh}-L_{g1},\qquad
--   \Lambda(L)=\max_h(\max_g\omega_{gh}-\min_g\omega_{gh}).$$
--
--   A mixture is $\alpha$-optimal if $F_M(p)\le F_M(q)+\alpha$ for every $q\in\Delta_k$. This is the usual minimum-based definition because the continuous objective attains its minimum. The max-entry norm is $\max_{g,h}|M_{gh}|$ and $d_q(M,L)=\tfrac12\operatorname{osc}(M-L)$, as in Eq. (2). A real surcharge is separable when $B_{gh}=b_g+c_h$; the admissible family $\mathcal S$ additionally requires its max-entry norm to be at most $5$, with no independent bounds on the factors.
--
--   The row span is $s_g=\max_hL_{gh}-\min_hL_{gh}$, the contrast class is $\mathcal C(L)=\{M\in[0,1]^{m\times k}:\omega(M)=\omega(L)\}$, and $\rho(L)=\tfrac14\max_{g\ne r}(2-s_g-s_r)$. Class diameter is the supremum of pairwise quotient distances; Chebyshev radius is the infimum of nonnegative radii of balls centered at arbitrary real tables that cover the class. Neither value is assumed to equal the paper's formula.
--
--   A bit query specifies $(B,h)$. A legal bit has a witnessing $\alpha$-optimal mixture with $p_h\ge1/2$ for bit $1$, or $p_h\le1/2$ for bit $0$. Witnesses are independent between calls. The module also defines the literal exposure and saturated-comparison surcharges, the row-midrange estimator, and $\eta=2^{-T}$, $z=\alpha+2\kappa$, $H=2z+\eta$.
--
--   These primitives provide the shared mathematical vocabulary for every result of this mission. **Formalization Note** The carriers use Mathlib real functions and its closed standard simplex; source column $1$ is Lean column $0$. Suprema over arrays are finite nonempty extrema in all theorem uses. The distinct-row maximum is used only with $m\ge2$.
-- source:
--   chaomeng chen, STOC 2027 submission #1429 (October 2026), Section 1.1, printed p.1 (PDF p.3); Section 2, Eqs. (1)–(2), printed pp.8–9 (PDF pp.10–11); Section 3.1, Eq. (3) and comparison surcharges, printed p.10 (PDF p.12); Theorem 4.2 radius definition, printed p.15 (PDF p.17)

import Mathlib
set_option autoImplicit false

noncomputable section

namespace MinimaxInterventions1429.Separable

abbrev Table (m k : ℕ) := Fin m → Fin k → ℝ

/-- The closed simplex, including its boundary. -/
abbrev Mixture (k : ℕ) := {p : Fin k → ℝ // p ∈ stdSimplex ℝ (Fin k)}

def InCube {m k : ℕ} (L : Table m k) : Prop :=
  ∀ g h, 0 ≤ L g h ∧ L g h ≤ 1

def entryNorm {m k : ℕ} (M : Table m k) : ℝ :=
  ⨆ g, ⨆ h, |M g h|

def osc {m k : ℕ} (M : Table m k) : ℝ :=
  (⨆ g, ⨆ h, M g h) - (⨅ g, ⨅ h, M g h)

/-- Equation (2); all theorems use nonempty finite arrays. -/
def quotientDist {m k : ℕ} (M L : Table m k) : ℝ := osc (M - L) / 2

def objective {m k : ℕ} (M : Table m k) (p : Mixture k) : ℝ :=
  ⨆ g, ∑ h, M g h * p.val h

/-- Comparison against every feasible mixture avoids a default-valued infimum.
For finite nonempty arrays the continuous objective attains its minimum on the simplex. -/
def Optimal {m k : ℕ} (M : Table m k) (α : ℝ) (p : Mixture k) : Prop :=
  ∀ q : Mixture k, objective M p ≤ objective M q + α

def IsSeparable {m k : ℕ} (B : Table m k) : Prop :=
  ∃ (b : Fin m → ℝ) (c : Fin k → ℝ), ∀ g h, B g h = b g + c h

def Allowed {m k : ℕ} (B : Table m k) : Prop := IsSeparable B ∧ entryNorm B ≤ 5

def contrasts {m k : ℕ} [NeZero k] (L : Table m k) : Table m k :=
  fun g h => L g h - L g 0

def interaction {m k : ℕ} [NeZero k] (L : Table m k) : ℝ :=
  ⨆ h, (⨆ g, contrasts L g h) - (⨅ g, contrasts L g h)

def rowSpan {m k : ℕ} (L : Table m k) (g : Fin m) : ℝ :=
  (⨆ h, L g h) - (⨅ h, L g h)

def ambiguityRadius {m k : ℕ} (L : Table m k) : ℝ :=
  sSup {s : ℝ | ∃ g r : Fin m, g ≠ r ∧ s = 2 - rowSpan L g - rowSpan L r} / 4

def contrastClass {m k : ℕ} [NeZero k] (L : Table m k) : Set (Table m k) :=
  {M | InCube M ∧ contrasts M = contrasts L}

def classDiameter {m k : ℕ} [NeZero k] (L : Table m k) : ℝ :=
  sSup {d : ℝ | ∃ M ∈ contrastClass L, ∃ N ∈ contrastClass L, d = quotientDist M N}

def classRadius {m k : ℕ} [NeZero k] (L : Table m k) : ℝ :=
  sInf {r : ℝ | 0 ≤ r ∧ ∃ C : Table m k, ∀ M ∈ contrastClass L, quotientDist C M ≤ r}

def centeredProfile {m k : ℕ} (w : Table m k) : Table m k :=
  fun g h => 1 / 2 + w g h - ((⨆ j, w g j) + (⨅ j, w g j)) / 2

structure Query (m k : ℕ) where
  surcharge : Table m k
  coordinate : Fin k

abbrev History (m k : ℕ) := List (Query m k × Bool)
abbrev BitOracle (m k : ℕ) := History m k → Query m k → Bool

def LegalBit {m k : ℕ} (L : Table m k) (α : ℝ) (q : Query m k) (v : Bool) : Prop :=
  ∃ p : Mixture k, Optimal (L + q.surcharge) α p ∧
    (if v then (1 : ℝ) / 2 ≤ p.val q.coordinate else p.val q.coordinate ≤ (1 : ℝ) / 2)

def AccurateHistory {m k : ℕ} (L : Table m k) (α : ℝ) (hist : History m k) : Prop :=
  ∀ q v, (q, v) ∈ hist → LegalBit L α q v

/-- Literal row-exposure surcharge of Lemma 3.2. Source column 1 is Lean column 0. -/
def exposed {m k : ℕ} [NeZero k] (g : Fin m) (h : Fin k) (t : ℝ) : Table m k :=
  fun r j => (if r = g then 0 else -3) +
    (if j = 0 then t else if j = h then 0 else 3)

/-- Literal saturated-comparison surcharge of Lemma 3.3. -/
def saturated {m k : ℕ} [NeZero k] (w : Table m k)
    (g r : Fin m) (h : Fin k) (t : ℝ) : Table m k :=
  fun s j =>
    (if s = g then -t - (w g h - w r h) / 2 else if s = r then 0 else -4) +
    (if j = 0 then 0 else if j = h then -(w g h + w r h) / 2 else 3)

def eta (T : ℕ) : ℝ := (2 : ℝ) ^ (-(T : ℤ))
def effectiveTolerance (α κ : ℝ) : ℝ := α + 2 * κ
def edgeError (α κ : ℝ) (T : ℕ) : ℝ := 2 * effectiveTolerance α κ + eta T

end MinimaxInterventions1429.Separable


