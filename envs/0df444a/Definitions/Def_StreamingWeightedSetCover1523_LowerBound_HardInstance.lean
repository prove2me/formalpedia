-- Prove2me | Definitions.Def_StreamingWeightedSetCover1523_LowerBound_HardInstance
-- name    : StreamingWeightedSetCover1523_LowerBound_HardInstance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:07:27.702512+00:00
-- url     : https://prove2.me/theorems/eb57d53f-aa0b-4bd9-a8a8-eb77c233f22b
-- title:
--   The two-weight hard instance: samplers, mask law $\mu_A$, parameters, good matrices, estimator and gap tasks
-- statement:
--   The hard instance of §§2–4.
--
--   **Sets.** Let $U=[v]\times\{0,1\}$ ($n=2v$ elements). A $v\times M$ binary matrix $A$ gives the cheap sets $C_j=\{(e,0),(e,1):A_{e,j}=1\}$ of weight $1$; a vector $V\in\mathbb F_2^v$ gives the transversal $T_V=\{(e,V_e):e\in[v]\}$. An instance has the $m=2M$ identifiers $C_1,\dots,C_M$ and $E_i=T_{V_i}$ ($i\le M$, weight $k$).
--
--   **Matrix law.** The entries of $A$ are independent Bernoulli$(\beta)$, $\beta=4/k$, $q=1-\beta$.
--
--   **Mask law.** With $N_e(K)=\sum_{j\in K}A_{e,j}$ and
--   $$h(c)=\frac{(-1)^c\binom4c}{\binom kc(\beta/q)^c}\ (0\le c\le4),\qquad h(c)=0\ (c>4),$$
--   given $A$ and a $k$-subset $K$ the mask bits are independent with $\Pr[Z_e=1\mid A,K]=(1-h(N_e(K)))/2$, and
--   $$\mu_A(z)=\mathbb E_K\prod_{e=1}^v\Pr[Z_e=z_e\mid A,K]$$
--   for $K$ a uniform $k$-subset of $[M]$.
--
--   **Samplers for fixed $A$.** Let $r=\lfloor M/2\rfloor$, $s=M-r$. Under NO ($P_0^A$) the vectors $V_1,\dots,V_M$ are independent uniform. Under YES ($P_1^A$) draw $W_1,\dots,W_M$ independent uniform, and independently $i^*$ uniform in the left block $[r]$, $j^*$ uniform in the right block, $K$ and $Z$ as above; keep $X=W_{i^*}$ and set $V_{j^*}=1+X+Z$ (addition mod 2). The unconditioned NO law $P_0$ also draws $A$.
--
--   **Parameters.** $d=\lfloor k^2/(64ev)\rfloor$ ($e=\exp 1$), $\lambda=k^2/M$, $\varepsilon=\lambda+e^{-d/120}$.
--
--   **Good matrices.** $A$ is good if the cheap family covers $U$ and for all densities $f,g$ on $\mathbb F_2^v$
--   $$\mathbb E_{X\sim U_v,Z\sim\mu_A}f(X)g(1+X+Z)\ge 1-\varepsilon-\tfrac{120}{d}(\mathrm{Ent}(f)+\mathrm{Ent}(g)).$$
--
--   **Two-party split.** Alice holds $V_{\le r}$, Bob $V_{>r}$; rectangle probabilities and protocol acceptance probabilities are computed for this split.
--
--   **Tasks over a fixed cheap family $C(A)$.** An instance over $C(A)$ is given by the $M$ expensive vectors. A randomized $p$-pass algorithm with $S$ bits of memory is a probability space of seeds, each selecting a machine with $2^S$ states that streams $V_1,\dots,V_M$ and may depend arbitrarily on $A$. It is an $\alpha$-estimator if on every instance over $C(A)$ its real answer $\widehat{\mathrm{OPT}}$ satisfies $\mathrm{OPT}\le\widehat{\mathrm{OPT}}\le\alpha\,\mathrm{OPT}$ with probability at least $2/3$; it solves the gap problem with advantage $\gamma$ if it answers YES on every instance with $\mathrm{OPT}\le 3k$ and NO on every instance with $\mathrm{OPT}>3\alpha k$, each with probability at least $1/2+\gamma$.
--
--   **Regime (1).** For an absolute constant $C_0$: eventually in $k$, $\alpha(k)\ge1$, $M\ge C_0k^2$ and $6\alpha e^{27\alpha}k\ln(2M+1)\le v$; and $v=o(k^2)$.
--
--   These definitions implement equations (1) and (3)–(8) literally; no conclusion of a lemma (goodness probability, cover gap, rectangle bound) is assumed in them.
--
--   **Formalization Note** Indices are 0-based. Probabilities are finite sums of explicit weights. When $\binom Mk=0$ or $d=0$ the Lean division convention $x/0=0$ applies; these cases do not occur in the regime (1) for large $k$. The estimator and gap definitions require the success events to be measurable.
-- source:
--   Ali Vakilian, Streaming Weighted Set Cover Requires (Nearly) Linear Space, STOC 2027 submission #1523 (October 2026), §2.1–2.4 (PDF pp. 7–11, eqs. (3)–(8)), §3 (PDF p. 13), §1.1 and §4 (PDF pp. 3, 16–18), eq. (1) (PDF p. 3); citation basis: submitted artifact, sha256 16f3c2dfc6183f4752aece654f17f2cb6a47fbe55659e6906ad7bd3524d6223f

import Definitions.Def_StreamingWeightedSetCover1523_LowerBound_Model

open MeasureTheory Filter
open scoped BigOperators ENNReal

namespace StreamingWeightedSetCover1523.LowerBound
noncomputable section

/-! The two-weight hard instance of Vakilian, STOC 2027 submission #1523, §§2–4
(PDF pp. 7–17, equations (1), (3)–(8)): sets, the cheap matrix law, the explicit YES/NO samplers,
the mask law `μ_A`, the parameters `d, λ, ε`, the good event, the two-party block split, and the
estimator and gap tasks over a fixed cheap family. -/

/-- Vectors in `F₂^v`; addition is coordinatewise modulo 2, `1` is the all-ones vector. -/
abbrev Vec (v : ℕ) := Fin v → ZMod 2

/-- A `v × M` binary matrix `A`, `A e j = true` iff `A_{e,j} = 1`. -/
abbrev Mat (v M : ℕ) := Fin v → Fin M → Bool

/-- The universe `U = [v] × {0,1}`, `n = 2v` elements. -/
abbrev Elt (v : ℕ) := Fin v × ZMod 2

/-- The `m = 2M` identifiers: cheap `C_j` (`inl j`) and expensive `E_i` (`inr i`). -/
abbrev Ident (M : ℕ) := Fin M ⊕ Fin M

/-- The cheap set `C_j = A_j × {0,1}`, `A_j = {e : A_{e,j} = 1}`. -/
def cheapSet {v M : ℕ} (A : Mat v M) (j : Fin M) : Finset (Elt v) :=
  Finset.univ.filter fun u => A u.1 j = true

/-- The transversal `T_x = {(e, x_e) : e ∈ [v]}`. -/
def transversal {v : ℕ} (x : Vec v) : Finset (Elt v) :=
  Finset.univ.filter fun u => u.2 = x u.1

/-- The instance with cheap matrix `A` and expensive vectors `V₁, …, V_M` (table of §2.1, PDF p. 6):
cheap sets of weight `1`, transversals of weight `k`. -/
def inst {v M : ℕ} (k : ℕ) (A : Mat v M) (V : Fin M → Vec v) : WSCInstance (Ident M) (Elt v) where
  sets := fun i => match i with
    | .inl j => cheapSet A j
    | .inr i => transversal (V i)
  weight := fun i => match i with
    | .inl _ => 1
    | .inr _ => (k : ℝ)

/-- The cheap family `C = C(A)` covers `U`. -/
def CheapCovers {v M : ℕ} (A : Mat v M) : Prop :=
  ∀ u : Elt v, ∃ j : Fin M, u ∈ cheapSet A j

/-- `β = 4/k`. -/
def beta (k : ℕ) : ℝ := 4 / (k : ℝ)

/-- Probability of the matrix `A` when its entries are independent Bernoulli(`4/k`). -/
def matWeight {v M : ℕ} (k : ℕ) (A : Mat v M) : ℝ :=
  ∏ e : Fin v, ∏ j : Fin M, if A e j = true then beta k else 1 - beta k

/-- `Pr_A[E]` over the initial draw of `A` with independent Bernoulli(`4/k`) entries. -/
def probA {v M : ℕ} (k : ℕ) (E : Mat v M → Prop) : ℝ := by
  classical
  exact ∑ A : Mat v M, if E A then matWeight k A else 0

/-- The function `h` of equation (4): `h(c) = (-1)^c C(4,c) / (C(k,c) (β/q)^c)` for `0 ≤ c ≤ 4`,
`q = 1 - β`, and `h(c) = 0` for `c > 4`. -/
def hfun (k c : ℕ) : ℝ :=
  if c ≤ 4 then
    (-1 : ℝ) ^ c * (Nat.choose 4 c : ℝ) /
      ((Nat.choose k c : ℝ) * (beta k / (1 - beta k)) ^ c)
  else 0

/-- `N_e(K) = ∑_{j ∈ K} A_{e,j}`, the coverage multiplicity of the index set `K` at `e`. -/
def coverCount {v M : ℕ} (A : Mat v M) (K : Finset (Fin M)) (e : Fin v) : ℕ :=
  (K.filter fun j => A e j = true).card

/-- `Pr[Z = z | A, K] = ∏_e Pr[Z_e = z_e | A, K]`, with `Pr[Z_e = 1 | A, K] = (1 - h(N_e(K)))/2`
(equation (3)). -/
def maskProb {v M : ℕ} (k : ℕ) (A : Mat v M) (K : Finset (Fin M)) (z : Vec v) : ℝ :=
  ∏ e : Fin v,
    if z e = 1 then (1 - hfun k (coverCount A K e)) / 2 else (1 + hfun k (coverCount A K e)) / 2

/-- `μ_A(z) = E_K ∏_e Pr[Z_e = z_e | A, K]` with `K` a uniform `k`-subset of `[M]` (equation (6)). -/
def mu {v M : ℕ} (k : ℕ) (A : Mat v M) (z : Vec v) : ℝ :=
  (∑ K ∈ (Finset.univ : Finset (Fin M)).powersetCard k, maskProb k A K z) /
    (Nat.choose M k : ℝ)

/-- `P₀^A`: under NO the expensive vectors are independent uniform on `F₂^v`, independent of `A`. -/
def noLaw {v M : ℕ} (_V : Fin M → Vec v) : ℝ :=
  1 / (2 : ℝ) ^ (M * v)

/-- `P₁^A`, the YES law of the expensive vectors for a fixed matrix (§2.2, PDF pp. 7–8): draw
`W₁, …, W_M` independent uniform; independently draw `i* ∈ [r]` and `j* ∈ {r+1, …, M}` uniformly
(`r = ⌊M/2⌋`, indices are 0-based here), a uniform `k`-subset `K`, and the mask `Z` by (3) given
`A, K`; keep `X = W_{i*}` and overwrite `V_{j*} = 1 + X + Z`. -/
def yesLaw {v M : ℕ} (k : ℕ) (A : Mat v M) (V : Fin M → Vec v) : ℝ := by
  classical
  exact (1 / (((M / 2 : ℕ) : ℝ) * ((M - M / 2 : ℕ) : ℝ))) *
    ∑ i : Fin M, ∑ j : Fin M,
      if i.val < M / 2 ∧ M / 2 ≤ j.val then
        (1 / (Nat.choose M k : ℝ)) *
          ∑ K ∈ (Finset.univ : Finset (Fin M)).powersetCard k, ∑ Z : Vec v,
            maskProb k A K Z *
              ∑ W : Fin M → Vec v,
                if Function.update W j (1 + W i + Z) = V then 1 / (2 : ℝ) ^ (M * v) else 0
      else 0

/-- `Pr_{P₀}[E]` under the unconditioned joint NO distribution of `(A, V₁, …, V_M)`. -/
def noJointProb {v M : ℕ} (k : ℕ) (E : Mat v M → (Fin M → Vec v) → Prop) : ℝ := by
  classical
  exact ∑ A : Mat v M, matWeight k A * ∑ V : Fin M → Vec v, if E A V then noLaw V else 0

/-- `d = ⌊k² / (64 e v)⌋` with `e = exp 1` (equation (8)). -/
def dParam (k v : ℕ) : ℕ :=
  ⌊(k : ℝ) ^ 2 / (64 * Real.exp 1 * (v : ℝ))⌋₊

/-- `λ = k² / M` (equation (8)). -/
def lam (k M : ℕ) : ℝ := (k : ℝ) ^ 2 / (M : ℝ)

/-- `ε = λ + e^{-d/120}` (equation (8)). -/
def eps (k v M : ℕ) : ℝ := lam k M + Real.exp (-(dParam k v : ℝ) / 120)

/-- `E_{X ∼ U_v, Z ∼ μ_A} f(X) g(1 + X + Z)`. -/
def pairCorr {v M : ℕ} (k : ℕ) (A : Mat v M) (f g : Vec v → ℝ) : ℝ :=
  ∑ x : Vec v, ∑ z : Vec v, (1 / (2 : ℝ) ^ v) * mu k A z * f x * g (1 + x + z)

/-- A good matrix (Lemma 2.2, PDF p. 10): the cheap family covers `U`, and inequality (9) holds for
every pair of densities `f, g` on `F₂^v`. -/
def Good {v M : ℕ} (k : ℕ) (A : Mat v M) : Prop :=
  CheapCovers A ∧
    ∀ f g : Vec v → ℝ, IsDensity f → IsDensity g →
      1 - eps k v M - (120 / (dParam k v : ℝ)) * (Ent f + Ent g) ≤ pairCorr k A f g

/-- Alice's block `V_{≤r} = (V₁, …, V_r)`, `r = ⌊M/2⌋`. -/
def leftBlock {v M : ℕ} (V : Fin M → Vec v) : Fin (M / 2) → Vec v :=
  fun i => V ⟨i.val, by omega⟩

/-- Bob's block `V_{>r} = (V_{r+1}, …, V_M)`, `s = M - r` vectors. -/
def rightBlock {v M : ℕ} (V : Fin M → Vec v) : Fin (M - M / 2) → Vec v :=
  fun j => V ⟨M / 2 + j.val, by omega⟩

/-- The two-party split of the expensive vectors. -/
def blocks {v M : ℕ} (V : Fin M → Vec v) : (Fin (M / 2) → Vec v) × (Fin (M - M / 2) → Vec v) :=
  (leftBlock V, rightBlock V)

/-- The probability of the rectangle `R × T` under a law of the expensive vectors. -/
def rectProb {v M : ℕ} (law : (Fin M → Vec v) → ℝ) (R : Set (Fin (M / 2) → Vec v))
    (T : Set (Fin (M - M / 2) → Vec v)) : ℝ := by
  classical
  exact ∑ V : Fin M → Vec v, if leftBlock V ∈ R ∧ rightBlock V ∈ T then law V else 0

/-- The answer `y` satisfies `OPT ≤ y ≤ α OPT` (§1.1, PDF p. 3). -/
def EstimateOK {ι U : Type} [Fintype ι] (I : WSCInstance ι U) (α y : ℝ) : Prop :=
  I.opt ≤ (y : WithTop ℝ) ∧ (y : WithTop ℝ) ≤ I.opt.map (fun t => α * t)

/-- A randomized `p`-pass `α`-estimator with `S` bits of memory for the instances over the fixed
cheap family `C(A)` (§1.1 and §4, PDF pp. 3, 15, 17): seeds `ω ∼ P` (all public and private
randomness, independent of the input) select a machine with state set `Fin (2^S)` that may depend
arbitrarily on `A`; it streams the `M` expensive sets `E₁, …, E_M` (as their vectors), and on every
instance over `C(A)` its answer satisfies `OPT ≤ answer ≤ α OPT` with probability at least `2/3`. -/
def IsEstimator {v M S : ℕ} (k : ℕ) (α : ℝ) (A : Mat v M) (p : ℕ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (alg : Ω → Machine M (Vec v) (Fin (2 ^ S)) ℝ) : Prop :=
  ∀ V : Fin M → Vec v,
    MeasurableSet {ω | EstimateOK (inst k A V) α ((alg ω).run p V)} ∧
      (2 / 3 : ℝ≥0∞) ≤ P {ω | EstimateOK (inst k A V) α ((alg ω).run p V)}

/-- A randomized `p`-pass algorithm with `S` bits of memory solves the gap problem for `C(A)` with
advantage `γ` (§4, PDF p. 15): on every instance over `C(A)` with `OPT ≤ 3k` it answers YES
(`true`), and on every instance with `OPT > 3αk` it answers NO (`false`), each with probability at
least `1/2 + γ`. -/
def SolvesGap {v M S : ℕ} (k : ℕ) (α γ : ℝ) (A : Mat v M) (p : ℕ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (alg : Ω → Machine M (Vec v) (Fin (2 ^ S)) Bool) : Prop :=
  ∀ V : Fin M → Vec v,
    ((inst k A V).opt ≤ ((3 * (k : ℝ) : ℝ) : WithTop ℝ) →
      MeasurableSet {ω | (alg ω).run p V = true} ∧
        ENNReal.ofReal (1 / 2 + γ) ≤ P {ω | (alg ω).run p V = true}) ∧
    (¬ (inst k A V).opt ≤ ((3 * α * (k : ℝ) : ℝ) : WithTop ℝ) →
      MeasurableSet {ω | (alg ω).run p V = false} ∧
        ENNReal.ofReal (1 / 2 + γ) ≤ P {ω | (alg ω).run p V = false})

/-- The parameter regime (1) for the absolute constant `C₀` (PDF p. 3): eventually in `k`,
`α(k) ≥ 1`, `M(k) ≥ C₀ k²` and `6 α e^{27α} k ln(2M + 1) ≤ v(k)`; and `v = o(k²)`. -/
def ParamsEq1 (C₀ : ℝ) (α : ℕ → ℝ) (M v : ℕ → ℕ) : Prop :=
  (∀ᶠ k : ℕ in atTop,
      1 ≤ α k ∧ C₀ * (k : ℝ) ^ 2 ≤ (M k : ℝ) ∧
        6 * α k * Real.exp (27 * α k) * (k : ℝ) * Real.log (2 * (M k : ℝ) + 1) ≤ (v k : ℝ)) ∧
    (fun k : ℕ => (v k : ℝ)) =o[atTop] (fun k : ℕ => (k : ℝ) ^ 2)

end
end StreamingWeightedSetCover1523.LowerBound


