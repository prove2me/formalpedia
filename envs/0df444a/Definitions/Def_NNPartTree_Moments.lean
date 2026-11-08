-- Prove2me | Definitions.Def_NNPartTree_Moments
-- name    : NNPartTree_Moments
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:08:17.44744+00:00
-- url     : https://prove2.me/theorems/07e2b80d-df2f-47ea-9eaa-e246d2f7c831
-- title:
--   Energy, kurtosis, approximation degree, the degree bound of Theorem 4, and the empirical law
-- statement:
--   For $F:\mathbb R^d\to\mathbb R$ and a law $\mathcal D$ on pairs, the **energy** and **kurtosis** are
--   $$R_{\mathcal D}(F)=\frac{\mathbf E_{(x,y)\sim\mathcal D}[(F(x)-F(y))^2]}{\mathrm{Var}_{y\sim\mathcal D_Y}[F(y)]},\qquad \gamma(F;M)=\frac{\mathbf E_{y\sim M}[(F(y)-\mu)^4]}{\mathrm{Var}_{y\sim M}[F(y)]^2},\quad\mu=\mathbf E_M[F].$$
--   Also $S(F)=\mathbf E_{\mathcal D}[|F(x)^2-F(y)^2|]$ and $\mathrm{tail}(G,t)=\Pr_{y\sim\mathcal D_Y}[G(y)\ge t]$.
--
--   A polynomial $A$ **approximates** $f$ to $\varepsilon$ if for all $\ell\in\{1,2,4\}$, $\mathbf E_{\mathcal D_X}|A-f|^\ell\le\varepsilon$ and $\mathbf E_{\mathcal D_Y}|A-f|^\ell\le\varepsilon$: one polynomial for both marginals and all $\ell$. The first hypothesis of Theorem 4 says that for all $\varepsilon>0$, $R,J\in\mathbb N$ and every $(R,J)$-halfspace function $h$ some polynomial of degree at most $(R\cdot 2^J/\varepsilon)^{c_1}$ approximates $h$ to $\varepsilon$.
--
--   A polynomial is **feasible** for $\Pi(\mathcal D,C)$ if $\mathbf E_{\mathcal D_Y}[A]=0$, $\mathbf E_{\mathcal D_Y}[A^2]=1$ and $\mathbf E_{\mathcal D_Y}[A^4]\le C$. For a sample $S=((x_i,y_i))_{i\le m}$ the same notions are taken over the uniform law on $S$, and $S\sim\mathcal D^m$ means $m$ independent samples.
--
--   **Formalization Note** The approximation moments are in $[0,\infty]$ (`∫⁻`), so a polynomial with infinite moments does not satisfy the bound. `energy` and `kurtosis` use Bochner integrals and a real division, so every statement bounding them also has positive variance and finite moments (`HasFiniteMoments`).
-- source:
--   Khanna, Padaki, Waingarten, Learning Partition Trees for Nearest Neighbor Search, arXiv:2607.09909 (held copy of 2026-11-03, sha256 d32992f2…), Definition 5.1, p.14; Definitions 5.2, 5.3, p.15; Definition 5.4, p.17; Definition 6.7, p.26; S(F), p.42; tail, p.43; first hypothesis of Theorem 4, p.27

import Mathlib
import Definitions.Def_NNPartTree_Cuts

open MeasureTheory
open scoped ENNReal

namespace NNPartTree

/-!
# Energy, kurtosis, approximation degree and the empirical law

S. Khanna, A. Padaki, E. Waingarten, *Learning Partition Trees for Nearest Neighbor Search*,
arXiv:2607.09909 (STOC 2027 submission), held copy of 2026-11-03, sha256 d32992f2…,
Definitions 5.1 (p.14), 5.2, 5.3 (p.15), 5.4 (p.17), 6.7 (p.26), and the functional `S(F)` (p.42).

**Formalization Note.**
* The moments of `|A − f|` in the approximation degree are measured with `∫⁻`, in `[0, ∞]`. A polynomial
  with infinite moments therefore does not satisfy the bound. A Bochner integral would return `0` and
  satisfy it for free.
* `energy` and `kurtosis` use Bochner integrals and a real division, so they are `0` on a zero variance
  and on non-integrable data. Each statement that bounds them from above therefore also has `0 < varOn`
  and `HasFiniteMoments`, as a hypothesis or as part of its conclusion.
* The degree bound `k(ε) ≤ (R · 2^J/ε)^{c₁}` of Theorem 4 is compared in `ℝ`.
* `empirical S` is the uniform law on the sample `S`: the paper's "we abuse notation to let S denote the
  uniform distribution over these samples" (p.15). So `err`, `bal`, `energy` on a sample are the same
  definitions. For `m = 0` it is the zero measure; every statement that uses it has `m ≥ 1`.
-/

variable {d : ℕ}

/-- The variance `Var_{y∼M}[F(y)]`. -/
noncomputable def varOn (M : Measure (Pt d)) (F : Pt d → ℝ) : ℝ :=
  ∫ y, (F y - ∫ y', F y' ∂M) ^ 2 ∂M

/-- The numerator `E_{(x,y)∼D}[(F(x) − F(y))²]` of the energy, also the objective of `Π`
(Definition 5.4, p.17). -/
noncomputable def pairEnergy (D : Measure (Pt d × Pt d)) (F : Pt d → ℝ) : ℝ :=
  ∫ z, (F z.1 - F z.2) ^ 2 ∂D

/-- The energy `R_D(F) = E[(F(x) − F(y))²] / Var_{D_Y}[F]` (Definition 5.2, p.15). -/
noncomputable def energy (D : Measure (Pt d × Pt d)) (F : Pt d → ℝ) : ℝ :=
  pairEnergy D F / varOn (marginalY D) F

/-- The kurtosis `γ(F; M) = E_M[(F − μ)⁴] / Var_M[F]²` (Definition 5.3, p.15). -/
noncomputable def kurtosis (M : Measure (Pt d)) (F : Pt d → ℝ) : ℝ :=
  (∫ y, (F y - ∫ y', F y' ∂M) ^ 4 ∂M) / varOn M F ^ 2

/-- The relaxation `S(F) = E_{(x,y)∼D}[|F(x)² − F(y)²|]` (p.42). -/
noncomputable def relaxedEnergy (D : Measure (Pt d × Pt d)) (F : Pt d → ℝ) : ℝ :=
  ∫ z, |F z.1 ^ 2 - F z.2 ^ 2| ∂D

/-- `tail(G, t) = Pr_{y∼D_Y}[G(y) ≥ t]` (p.43). -/
noncomputable def tail (D : Measure (Pt d × Pt d)) (G : Pt d → ℝ) (t : ℝ) : ℝ :=
  (marginalY D {y | t ≤ G y}).toReal

/-- The moments that appear in `R_D(F)` and `γ(F; D_Y)` are finite: `(F(x) − F(y))²` is
`D`-integrable and `F(y)⁴` is `D_Y`-integrable. On a probability measure the lower moments of
`F(y)` follow. -/
def HasFiniteMoments (D : Measure (Pt d × Pt d)) (F : Pt d → ℝ) : Prop :=
  Integrable (fun z : Pt d × Pt d => (F z.1 - F z.2) ^ 2) D ∧
    Integrable (fun y => F y ^ 4) (marginalY D)

/-- `A` approximates `f` to `ε` under both marginals of `D`: for all `ℓ ∈ {1, 2, 4}`,
`E_{D_X}|A − f|^ℓ ≤ ε` and `E_{D_Y}|A − f|^ℓ ≤ ε` (Definition 5.1, p.14). One `A` for both marginals and
all `ℓ`. -/
def MomentBound (D : Measure (Pt d × Pt d)) (f : Pt d → ℝ) (A : MvPolynomial (Fin d) ℝ) (ε : ℝ) :
    Prop :=
  ∀ ℓ ∈ ({1, 2, 4} : Finset ℕ),
    ∫⁻ x, ‖peval A x - f x‖ₑ ^ ℓ ∂(marginalX D) ≤ ENNReal.ofReal ε ∧
      ∫⁻ y, ‖peval A y - f y‖ₑ ^ ℓ ∂(marginalY D) ≤ ENNReal.ofReal ε

/-- Some polynomial of degree at most `k` approximates `f` to `ε`: the content of "`D` has
`F`-approximation degree `k(·)`" at one `f` and one `ε`, with `k = k(ε)` (Definition 5.1, p.14). -/
def ApproxAt (D : Measure (Pt d × Pt d)) (f : Pt d → ℝ) (ε : ℝ) (k : ℕ) : Prop :=
  ∃ A : MvPolynomial (Fin d) ℝ, A.totalDegree ≤ k ∧ MomentBound D f A ε

/-- The first hypothesis of Theorem 4, p.27: for any `ε > 0` and `R, J ∈ ℕ`, `D` has `(R, J)`-halfspace
approximation degree `k(ε) ≤ (R · 2^J/ε)^{c₁}` (Definitions 5.1, 6.7). -/
def HasDegreeBound (D : Measure (Pt d × Pt d)) (c₁ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ (R J : ℕ) (h : Pt d → ℝ), IsRJFunction R J h →
    ∃ A : MvPolynomial (Fin d) ℝ,
      (A.totalDegree : ℝ) ≤ ((R : ℝ) * 2 ^ J / ε) ^ c₁ ∧ MomentBound D h A ε

/-- The uniform law on a sample `S = ((x₁, y₁), …, (x_m, y_m))` (p.15). -/
noncomputable def empirical {m : ℕ} (S : Fin m → Pt d × Pt d) : Measure (Pt d × Pt d) :=
  (m : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (S i)

/-- `S ∼ D^m`: `m` independent samples (p.15). -/
noncomputable def sampleProduct (D : Measure (Pt d × Pt d)) (m : ℕ) :
    Measure (Fin m → Pt d × Pt d) :=
  Measure.pi fun _ => D

instance (D : Measure (Pt d × Pt d)) [IsProbabilityMeasure D] (m : ℕ) :
    IsProbabilityMeasure (sampleProduct D m) := by
  unfold sampleProduct; infer_instance

/-- `A` is feasible for `Π(S, C)` (Definition 5.4, p.17): `E_{S_Y}[A] = 0`, `E_{S_Y}[A²] = 1` and
`E_{S_Y}[A⁴] ≤ C`, with finite moments so that the integrals mean what they say. The objective value
is `pairEnergy S A`, and the degree constraint is stated with the polynomial. -/
def PiFeasible (S : Measure (Pt d × Pt d)) (C : ℝ) (A : MvPolynomial (Fin d) ℝ) : Prop :=
  HasFiniteMoments S (peval A) ∧
    ∫ y, peval A y ∂(marginalY S) = 0 ∧
    ∫ y, peval A y ^ 2 ∂(marginalY S) = 1 ∧
    ∫ y, peval A y ^ 4 ∂(marginalY S) ≤ C

end NNPartTree


