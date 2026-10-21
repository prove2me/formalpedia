-- Prove2me | Definitions.Def_ExtFSMFG_Existence_Model
-- name    : ExtFSMFG_Existence_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:00:36.684529+00:00
-- url     : https://prove2.me/theorems/defcf136-8a3e-4181-91d3-51a68c568beb
-- title:
--   §§2–3, (1), (5)–(16), (19)–(21), pp. 3–9 — canonical finite-state path space, reference chain, controlled measures, cost, Nash equilibrium, Hamiltonian, Assumptions 2.2, 2.7, 3.4
-- statement:
--   These are the objects of the weak formulation of the extended finite state mean field game of Carmona and Wang.
--
--   1. **States and paths.** The $m$ states are identified with the basis vectors $e_1,\dots,e_m$ of $\mathbb R^m$ (in Lean, with $i\in\{1,\dots,m\}$). The **canonical space** $\Omega$ is the set of càdlàg paths $[0,T]\to E=\{e_1,\dots,e_m\}$ that are continuous at $T$; $X_t(\omega)=\omega_t$ is the canonical process, $X_{t-}$ its left limit ($X_{0-}=X_0$), $\mathcal F=\sigma\{X_t,\ t\le T\}$ and $\mathcal F_t=\sigma\{X_s,\ s\le t\}$ its natural filtration.
--   2. **Reference measure.** $Q^0$ is the $m\times m$ matrix with diagonal entries $-(m-1)$ and off-diagonal entries $1$. A measure $\mathbb P$ on $\Omega$ is the reference measure for an initial law $p^\circ\in\mathcal S$ if under $\mathbb P$ the process $X$ is a continuous-time Markov chain with initial law $p^\circ$ and rate matrix $Q^0$, i.e. for $0=t_0<t_1<\dots<t_k\le T$,
--   $$\mathbb P(X_{t_0}=e_{i_0},\dots,X_{t_k}=e_{i_k})=p^\circ_{i_0}\prod_{r=1}^k\big(e^{(t_r-t_{r-1})Q^0}\big)_{i_{r-1}i_r}.$$
--   3. **Controls and measures of controls.** $\mathcal S=\{p\in\mathbb R^m:\ p_i\ge0,\ \sum_ip_i=1\}$; $A\subseteq\mathbb R^l$ is the control set; $\mathcal P(A)$ is the set of probability measures on $A$ with the weak topology and its Borel $\sigma$-field; $\mathcal W_1(\nu,\nu')=\inf_\pi\int\|a-a'\|\,\pi(da,da')$ over couplings $\pi$ of $\nu,\nu'$. A **strategy** $\alpha\in\mathbb A$ is an $\mathbb F$-predictable process with $\alpha_t\in A$ for $t\in[0,T]$. The seminorm $\|z\|_{e_i}=(\sum_{j\neq i}|z_j-z_i|^2)^{1/2}$ and the Euclidean norm $\|\cdot\|$ on $\mathbb R^m$ are used in the Lipschitz conditions.
--   4. **Controlled measure.** Given rates $q(t,i,j,\alpha,p,\nu)$, a strategy $\alpha$ and flows $p:[0,T]\to\mathcal S$, $\nu:[0,T]\to\mathcal P(A)$, the measure $\mathbb Q^{(\alpha,p,\nu)}$ has density with respect to $\mathbb P$ the Doléans-Dade exponential $\mathcal E(L^{(\alpha,p,\nu)})_T$ of (5)–(7):
--   $$\frac{d\mathbb Q^{(\alpha,p,\nu)}}{d\mathbb P}=\exp\Big(-\int_0^T\sum_{j\neq X_{t-}}\big(q(t,X_{t-},j,\alpha_t,p_t,\nu_t)-1\big)\,dt\Big)\prod_{t\in(0,T],\,X_t\neq X_{t-}}q(t,X_{t-},X_t,\alpha_t,p_t,\nu_t).$$
--   5. **Cost and equilibrium.** $J(\alpha,p,\nu)=\mathbb E^{\mathbb Q^{(\alpha,p,\nu)}}\big[\int_0^Tf(t,X_t,\alpha_t,p_t,\nu_t)\,dt+g(X_T,p_T)\big]$ (12). A triple $(\alpha^*,p^*,\nu^*)$ is a **Nash equilibrium** (Definition 2.8) if $p^*,\nu^*$ are measurable on $[0,T]$, $p^*_t\in\mathcal S$, $\alpha^*\in\mathbb A$, $J(\alpha^*,p^*,\nu^*)\le J(\alpha,p^*,\nu^*)$ for every $\alpha\in\mathbb A$ (14), and for every $t\in[0,T]$: $p^*_t=(\mathbb Q^{(\alpha^*,p^*,\nu^*)}[X_t=e_i])_{i}$ (15) and $\nu^*_t$ is the law of $\alpha^*_t$ under $\mathbb Q^{(\alpha^*,p^*,\nu^*)}$ (16).
--   6. **Hamiltonian.** $H_i(t,z,\alpha,p,\nu)=f(t,e_i,\alpha,p,\nu)+\sum_{j\neq i}(z_j-z_i)(q(t,i,j,\alpha,p,\nu)-1)$ (20) and $\hat H_i(t,z,p,\nu)=\inf_{\alpha\in A}H_i(t,z,\alpha,p,\nu)$.
--   7. **Assumptions.** *Assumption 2.2*: (i) $Q(t,\alpha,p,\nu)$ is a Q-matrix ($q_{ij}\ge0$ for $i\ne j$, $\sum_{j\ne i}q_{ij}=-q_{ii}$); (ii) there are $C_1,C_2>0$ with $C_1<q(t,i,j,\alpha,p,\nu)<C_2$ for $i\neq j$; (iii) $|q(t,i,j,\alpha,p,\nu)-q(t,i,j,\alpha',p',\nu')|\le C(\|\alpha-\alpha'\|+\|p-p'\|+\mathcal W_1(\nu,\nu'))$. *Assumption 2.7*: the same Lipschitz bound (10) for $f$, and $|g(e_i,p)-g(e_i,p')|\le C\|p-p'\|$ (11). *Assumption 3.4* (for a given $\hat a$): (i) $\hat a_i(t,z,p)\in A$ is the unique minimizer of $\alpha\mapsto H_i(t,z,\alpha,p,\nu)$ for every $\nu$; (ii) $\hat a_i$ is measurable on $[0,T]\times\mathbb R^m\times\mathcal S$ and $\|\hat a_i(t,z,p)-\hat a_i(t,z',p')\|\le C_1\|z-z'\|_{e_i}+(C_1+C_2\|z\|_{e_i})\|p-p'\|$ (21). All quantifiers range over $t\in[0,T]$, $\alpha\in A$, $p\in\mathcal S$, $\nu\in\mathcal P(A)$.
--   8. **Regularity (added, disclosed).** $q$ and $f$ are jointly measurable on $[0,T]\times A\times\mathcal S\times\mathcal P(A)$, and $f$ is bounded there.
--
--   These definitions are shared by the goal (Theorem 4.1) and all milestones of the mission.
--
--   **Formalization Note** Time is indexed by $\mathbb R_{\ge0}$ and paths are frozen after $T$, which puts them in bijection with the paper's paths on $[0,T]$; the filtration and predictability are Mathlib's (`Filtration`, `IsStronglyPredictable`). The reference measure is a hypothesis (`IsReference`), not a construction. The density is the closed form of $\mathcal E(L^{(\alpha,p,\nu)})_T$: $L$ has jumps $q(t,X_{t-},X_t,\dots)-1$ by (6) and drift $-\sum_{j\ne X_{t-}}(q-1)\,dt$ (by the identity $\psi^+_t(e_j-X_{t-})=\frac{m-1}{m}e_j-\sum_{k\neq j}\frac1me_k$ of p. 5), so no pseudo-inverse or stochastic integral is needed. $\hat a$ is an argument of Assumption 3.4, which is faithful because 3.4(i) determines it on $[0,T]\times\mathbb R^m\times\mathcal S$. The measurability and boundedness in item 8 are used but not stated by the paper (they make (5), (12) and the BSDE drivers meaningful). Law (16) is stated as equality of measures on $\mathbb R^l$ (push-forward of $\nu^*_t$ by $A\subseteq\mathbb R^l$).
-- source:
--   Carmona & Wang, A Probabilistic Approach to Extended Finite State Mean Field Games, arXiv:1808.07635v1, pp. 3–9, §2.2 (1), Assumption 2.2, (5)–(7), §2.3 Assumption 2.7, (12), Definition 2.8 (14)–(16), §3.2 (19)–(20), Assumption 3.4 (21)

import Mathlib

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace ExtFSMFG.Existence

noncomputable section

/-! ### The canonical space (§2.2, p. 3) -/

/-- A sample path of the chain: a map `ω : ℝ≥0 → Fin m` (state `i` stands for the basis vector
`eᵢ ∈ ℝᵐ`) that is frozen after `T` (`ω t = ω (min t T)`), right continuous with left limits, and
continuous at `T` (`X_{T−} = X_T`). Paths of this kind are in bijection with the càdlàg functions
`[0, T] → E` that are continuous at `T`. -/
def IsPath (m : ℕ) (T : ℝ≥0) (ω : ℝ≥0 → Fin m) : Prop :=
  (∀ t, ω t = ω (min t T)) ∧ (∀ t, ContinuousWithinAt ω (Set.Ici t) t) ∧
    (∀ t, ∃ x, Tendsto ω (𝓝[<] t) (𝓝 x)) ∧ ContinuousAt ω T

/-- The canonical space `Ω` of càdlàg paths `[0, T] → E` continuous at `T` (p. 3). -/
def Omega (m : ℕ) (T : ℝ≥0) : Type := {ω : ℝ≥0 → Fin m // IsPath m T ω}

/-- `ℱ = ℱ_T = σ{X_t, t ≤ T}`: the σ-algebra generated by the coordinates. -/
instance (m : ℕ) (T : ℝ≥0) : MeasurableSpace (Omega m T) :=
  inferInstanceAs (MeasurableSpace {ω : ℝ≥0 → Fin m // IsPath m T ω})

variable {m : ℕ} {T : ℝ≥0}

/-- The canonical process `X_t(ω) := ω_t`. -/
def Xc (t : ℝ≥0) (ω : Omega m T) : Fin m := ω.1 t

/-- The left limit `X_{t−}(ω)` (equal to `X_0` at `t = 0`). -/
def Xm (t : ℝ≥0) (ω : Omega m T) : Fin m := Function.leftLim ω.1 t

lemma measurable_Xc (t : ℝ≥0) : Measurable (Xc (m := m) (T := T) t) :=
  (measurable_pi_apply t).comp measurable_subtype_coe

/-- The natural filtration `ℱ_t := σ{X_s, s ≤ t}` of the canonical process. -/
def filt (m : ℕ) (T : ℝ≥0) : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Omega m T)) where
  seq t := ⨆ (s : ℝ≥0) (_ : s ≤ t), MeasurableSpace.comap (Xc (m := m) (T := T) s) inferInstance
  mono' _ _ hst := iSup₂_mono' fun s hs => ⟨s, hs.trans hst, le_rfl⟩
  le' _ := iSup₂_le fun s _ => (measurable_Xc s).comap_le

/-- The rate matrix `Q⁰` of the reference chain: diagonal entries `−(m − 1)`, off-diagonal
entries `1` (p. 3). -/
def Q0 (m : ℕ) : Matrix (Fin m) (Fin m) ℝ := fun i j => if i = j then -((m : ℝ) - 1) else 1

/-- The reference measure `P` (p. 3): under `P` the canonical process is a continuous-time Markov
chain with initial law `p°` and rate matrix `Q⁰`, i.e. its finite-dimensional distributions are
`P(X_{t₀} = i₀, …, X_{t_k} = i_k) = p°(i₀) ∏_{r=1}^k (exp((t_r − t_{r−1}) Q⁰))_{i_{r−1} i_r}`
for `0 = t₀ < t₁ < … < t_k ≤ T`. -/
def IsReference (T : ℝ≥0) (p₀ : stdSimplex ℝ (Fin m)) (P : Measure (Omega m T)) : Prop :=
  ∀ (k : ℕ) (t : Fin (k + 1) → ℝ≥0) (i : Fin (k + 1) → Fin m),
    t 0 = 0 → StrictMono t → t (Fin.last k) ≤ T →
      P {ω | ∀ r, Xc (t r) ω = i r} =
        ENNReal.ofReal (p₀.1 (i 0) * ∏ r : Fin k,
          NormedSpace.exp ((((t r.succ : ℝ) - (t r.castSucc : ℝ)) • Q0 m : Matrix (Fin m) (Fin m) ℝ))
            (i r.castSucc) (i r.succ))

/-! ### Controls, the simplex and `P(A)` (pp. 4–5) -/

/-- The Euclidean norm `‖v‖ = (Σᵢ vᵢ²)^{1/2}` on `ℝᵐ` (used for `‖p − p′‖`). -/
def eucl (v : Fin m → ℝ) : ℝ := Real.sqrt (∑ i, v i ^ 2)

/-- The stochastic seminorm `‖z‖_{eᵢ} := (Σ_{j≠i} |z_j − zᵢ|²)^{1/2}` (p. 5). -/
def seminormE (i : Fin m) (z : Fin m → ℝ) : ℝ :=
  Real.sqrt (∑ j ∈ Finset.univ.erase i, (z j - z i) ^ 2)

variable {l : ℕ}

/-- `P(A)`: probability measures on the control set `A ⊆ ℝˡ`, with the weak topology and its
Borel σ-algebra `B(P(A))`. -/
def PA (A : Set (EuclideanSpace ℝ (Fin l))) : Type := ProbabilityMeasure A

instance (A : Set (EuclideanSpace ℝ (Fin l))) : TopologicalSpace (PA A) :=
  inferInstanceAs (TopologicalSpace (ProbabilityMeasure A))

instance (A : Set (EuclideanSpace ℝ (Fin l))) : MeasurableSpace (PA A) := borel (PA A)

instance (A : Set (EuclideanSpace ℝ (Fin l))) : BorelSpace (PA A) := ⟨rfl⟩

/-- The underlying measure on `ℝˡ` of `ν ∈ P(A)` (push-forward by the inclusion `A ⊆ ℝˡ`). -/
def PA.toMeasureE {A : Set (EuclideanSpace ℝ (Fin l))} (ν : PA A) :
    Measure (EuclideanSpace ℝ (Fin l)) :=
  (ν : ProbabilityMeasure A).toMeasure.map Subtype.val

/-- The 1-Wasserstein distance `W₁(ν, ν′) = inf_π ∫ ‖a − a′‖ π(da, da′)`, the infimum over the
couplings `π` of `ν` and `ν′` (probability measures on `A × A` with marginals `ν`, `ν′`). -/
def W1 {A : Set (EuclideanSpace ℝ (Fin l))} (ν ν' : PA A) : ℝ :=
  sInf {c | ∃ π : Measure (A × A), IsProbabilityMeasure π ∧
    π.map Prod.fst = (ν : ProbabilityMeasure A).toMeasure ∧
    π.map Prod.snd = (ν' : ProbabilityMeasure A).toMeasure ∧
    c = ∫ x, ‖(x.1 : EuclideanSpace ℝ (Fin l)) - x.2‖ ∂π}

/-- A `Q`-matrix: `Q_{ij} ≥ 0` for `i ≠ j` and `Σ_{j≠i} Q_{ij} = −Q_{ii}` (p. 4). -/
def IsQMatrix (Q : Fin m → Fin m → ℝ) : Prop :=
  (∀ i j, i ≠ j → 0 ≤ Q i j) ∧ ∀ i, ∑ j ∈ Finset.univ.erase i, Q i j = -Q i i

/-- The player's strategy set `𝔸` (p. 5): `𝔽`-predictable processes with `α_t ∈ A` for
`t ∈ [0, T]`. -/
def IsStrategy (T : ℝ≥0) (A : Set (EuclideanSpace ℝ (Fin l)))
    (α : ℝ≥0 → Omega m T → EuclideanSpace ℝ (Fin l)) : Prop :=
  IsStronglyPredictable (filt m T) α ∧ ∀ t ≤ T, ∀ ω, α t ω ∈ A

/-! ### The controlled probability measure (5)–(7) -/

/-- The jump times of a path in `(0, T]`: `{t ∈ (0, T] : X_t ≠ X_{t−}}` (finite for every path). -/
def jumpSet (ω : Omega m T) : Set ℝ≥0 := {t | 0 < t ∧ t ≤ T ∧ Xc t ω ≠ Xm t ω}

/-- The Doléans-Dade exponential `ℰ(L)_T` of the martingale `L_t = ∫₀ᵗ X*_{s−}(R_s − Q⁰)ψ⁺_s d𝓜_s`
for a predictable rate field `R_s(ω) = [r(s, ω, i, j)]`, in closed form: `L` has jumps
`r(t, X_{t−}, X_t) − 1` at the jumps of `X` and drift `−Σ_{j≠X_{t−}} (r(t, X_{t−}, j) − 1) dt`, so
`ℰ(L)_T = exp(−∫₀ᵀ Σ_{j≠X_{t−}} (r(t, X_{t−}, j) − 1) dt) · ∏_{t ∈ (0,T], X_t ≠ X_{t−}} r(t, X_{t−}, X_t)`. -/
def densityR (T : ℝ≥0) (r : ℝ≥0 → Omega m T → Fin m → Fin m → ℝ) (ω : Omega m T) : ℝ :=
  Real.exp (-∫ t in Set.Icc (0 : ℝ) T,
      ∑ j ∈ Finset.univ.erase (Xm t.toNNReal ω), (r t.toNNReal ω (Xm t.toNNReal ω) j - 1)) *
    ∏ᶠ (t : ℝ≥0) (_ : t ∈ jumpSet ω), r t ω (Xm t ω) (Xc t ω)

/-- `dQ^(α,p,ν)/dP = ℰ(L^(α,p,ν))_T` (5)–(7), with rates `q(t, i, j, α_t, p_t, ν_t)`. -/
def density {A : Set (EuclideanSpace ℝ (Fin l))}
    (q : ℝ≥0 → Fin m → Fin m → EuclideanSpace ℝ (Fin l) → (Fin m → ℝ) → PA A → ℝ)
    (α : ℝ≥0 → Omega m T → EuclideanSpace ℝ (Fin l)) (p : ℝ≥0 → Fin m → ℝ) (ν : ℝ≥0 → PA A) :
    Omega m T → ℝ :=
  densityR T (fun t ω i j => q t i j (α t ω) (p t) (ν t))

/-- The controlled probability measure `Q^(α,p,ν)` of (7). -/
def Qctrl {A : Set (EuclideanSpace ℝ (Fin l))} (P : Measure (Omega m T))
    (q : ℝ≥0 → Fin m → Fin m → EuclideanSpace ℝ (Fin l) → (Fin m → ℝ) → PA A → ℝ)
    (α : ℝ≥0 → Omega m T → EuclideanSpace ℝ (Fin l)) (p : ℝ≥0 → Fin m → ℝ) (ν : ℝ≥0 → PA A) :
    Measure (Omega m T) :=
  P.withDensity fun ω => ENNReal.ofReal (density q α p ν ω)

/-! ### Cost and Nash equilibrium (12)–(16) -/

/-- The cost `J(α, p, ν) := E^{Q^(α,p,ν)}[∫₀ᵀ f(t, X_t, α_t, p_t, ν_t) dt + g(X_T, p_T)]` (12). -/
def Jcost {A : Set (EuclideanSpace ℝ (Fin l))} (P : Measure (Omega m T))
    (q : ℝ≥0 → Fin m → Fin m → EuclideanSpace ℝ (Fin l) → (Fin m → ℝ) → PA A → ℝ)
    (f : ℝ≥0 → Fin m → EuclideanSpace ℝ (Fin l) → (Fin m → ℝ) → PA A → ℝ)
    (g : Fin m → (Fin m → ℝ) → ℝ)
    (α : ℝ≥0 → Omega m T → EuclideanSpace ℝ (Fin l)) (p : ℝ≥0 → Fin m → ℝ) (ν : ℝ≥0 → PA A) : ℝ :=
  ∫ ω, ((∫ t in Set.Icc (0 : ℝ) T,
      f t.toNNReal (Xc t.toNNReal ω) (α t.toNNReal ω) (p t.toNNReal) (ν t.toNNReal)) +
    g (Xc T ω) (p T)) ∂(Qctrl P q α p ν)

/-- Definition 2.8 (p. 7): `(α*, p*, ν*)` is a Nash equilibrium for the weak formulation:
`p* : [0, T] → S` and `ν* : [0, T] → P(A)` are measurable, `α* ∈ 𝔸`, and
(i) `α*` minimizes `J(·, p*, ν*)` over `𝔸` (14);
(ii) for each `t ∈ [0, T]`, `p*_t = (Q^(α*,p*,ν*)[X_t = eᵢ])ᵢ` (15) and `ν*_t = Q^(α*,p*,ν*)_{#α*_t}` (16). -/
def IsNashEq (T : ℝ≥0) (A : Set (EuclideanSpace ℝ (Fin l))) (P : Measure (Omega m T))
    (q : ℝ≥0 → Fin m → Fin m → EuclideanSpace ℝ (Fin l) → (Fin m → ℝ) → PA A → ℝ)
    (f : ℝ≥0 → Fin m → EuclideanSpace ℝ (Fin l) → (Fin m → ℝ) → PA A → ℝ)
    (g : Fin m → (Fin m → ℝ) → ℝ)
    (α : ℝ≥0 → Omega m T → EuclideanSpace ℝ (Fin l)) (p : ℝ≥0 → Fin m → ℝ) (ν : ℝ≥0 → PA A) :
    Prop :=
  (Measurable fun t : Set.Icc (0 : ℝ≥0) T => p t) ∧ (∀ t ≤ T, p t ∈ stdSimplex ℝ (Fin m)) ∧
  (Measurable fun t : Set.Icc (0 : ℝ≥0) T => ν t) ∧ IsStrategy T A α ∧
  (∀ β, IsStrategy T A β → Jcost P q f g α p ν ≤ Jcost P q f g β p ν) ∧
  (∀ t ≤ T, ∀ i, p t i = (Qctrl P q α p ν {ω | Xc t ω = i}).toReal) ∧
  (∀ t ≤ T, (ν t).toMeasureE = (Qctrl P q α p ν).map (α t))

/-! ### Hamiltonian (19)–(20) and the standing assumptions -/

/-- The reduced Hamiltonian (20):
`Hᵢ(t, z, α, p, ν) = f(t, eᵢ, α, p, ν) + Σ_{j≠i} (z_j − zᵢ)(q(t, i, j, α, p, ν) − 1)`, which is
`H(t, eᵢ, z, α, p, ν)` of (19). -/
def Hi {A : Set (EuclideanSpace ℝ (Fin l))}
    (q : ℝ≥0 → Fin m → Fin m → EuclideanSpace ℝ (Fin l) → (Fin m → ℝ) → PA A → ℝ)
    (f : ℝ≥0 → Fin m → EuclideanSpace ℝ (Fin l) → (Fin m → ℝ) → PA A → ℝ)
    (t : ℝ≥0) (i : Fin m) (z : Fin m → ℝ) (a : EuclideanSpace ℝ (Fin l)) (p : Fin m → ℝ)
    (ν : PA A) : ℝ :=
  f t i a p ν + ∑ j ∈ Finset.univ.erase i, (z j - z i) * (q t i j a p ν - 1)

/-- The minimized Hamiltonian `Ĥᵢ(t, z, p, ν) := inf_{α∈A} Hᵢ(t, z, α, p, ν)` (p. 8); by (24),
`Ĥ(t, eᵢ, z, p, ν) = Ĥᵢ(t, z, p, ν)`. -/
def Hhat {A : Set (EuclideanSpace ℝ (Fin l))}
    (q : ℝ≥0 → Fin m → Fin m → EuclideanSpace ℝ (Fin l) → (Fin m → ℝ) → PA A → ℝ)
    (f : ℝ≥0 → Fin m → EuclideanSpace ℝ (Fin l) → (Fin m → ℝ) → PA A → ℝ)
    (t : ℝ≥0) (i : Fin m) (z : Fin m → ℝ) (p : Fin m → ℝ) (ν : PA A) : ℝ :=
  ⨅ a : A, Hi q f t i z a p ν

/-- Assumption 2.2 (p. 4): (i) `Q(t, α, p, ν)` is a Q-matrix; (ii) `0 < C₁ < q(t, i, j, α, p, ν) < C₂`
for `i ≠ j`; (iii) `q` is Lipschitz in `(α, p, ν)` with `W₁` in `ν`. -/
def Assumption22 (T : ℝ≥0) (A : Set (EuclideanSpace ℝ (Fin l)))
    (q : ℝ≥0 → Fin m → Fin m → EuclideanSpace ℝ (Fin l) → (Fin m → ℝ) → PA A → ℝ) : Prop :=
  (∀ t ≤ T, ∀ a ∈ A, ∀ p ∈ stdSimplex ℝ (Fin m), ∀ ν, IsQMatrix fun i j => q t i j a p ν) ∧
  (∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ t ≤ T, ∀ i j, i ≠ j → ∀ a ∈ A, ∀ p ∈ stdSimplex ℝ (Fin m),
    ∀ ν, C₁ < q t i j a p ν ∧ q t i j a p ν < C₂) ∧
  (∃ C : ℝ, 0 < C ∧ ∀ t ≤ T, ∀ i j, ∀ a ∈ A, ∀ a' ∈ A, ∀ p ∈ stdSimplex ℝ (Fin m),
    ∀ p' ∈ stdSimplex ℝ (Fin m), ∀ ν ν',
      |q t i j a p ν - q t i j a' p' ν'| ≤ C * (‖a - a'‖ + eucl (p - p') + W1 ν ν'))

/-- Assumption 2.7 (p. 6): `f` is Lipschitz in `(α, p, ν)` (10) and `g` is Lipschitz in `p` (11),
with one constant `C`. -/
def Assumption27 (T : ℝ≥0) (A : Set (EuclideanSpace ℝ (Fin l)))
    (f : ℝ≥0 → Fin m → EuclideanSpace ℝ (Fin l) → (Fin m → ℝ) → PA A → ℝ)
    (g : Fin m → (Fin m → ℝ) → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    (∀ t ≤ T, ∀ i, ∀ a ∈ A, ∀ a' ∈ A, ∀ p ∈ stdSimplex ℝ (Fin m), ∀ p' ∈ stdSimplex ℝ (Fin m),
      ∀ ν ν', |f t i a p ν - f t i a' p' ν'| ≤ C * (‖a - a'‖ + eucl (p - p') + W1 ν ν')) ∧
    (∀ i, ∀ p ∈ stdSimplex ℝ (Fin m), ∀ p' ∈ stdSimplex ℝ (Fin m),
      |g i p - g i p'| ≤ C * eucl (p - p'))

/-- Assumption 3.4 (p. 8), for a given candidate minimizer `â`:
(i) for all `t ∈ [0, T]`, `i`, `z ∈ ℝᵐ`, `p ∈ S`, `ν ∈ P(A)`, `âᵢ(t, z, p) ∈ A` is the unique
minimizer of `α ↦ Hᵢ(t, z, α, p, ν)` over `A` (it has no `ν` argument);
(ii) `âᵢ` is measurable on `[0, T] × ℝᵐ × S` and satisfies (21) with `C₁ > 0`, `C₂ ≥ 0`. -/
def Assumption34 (T : ℝ≥0) (A : Set (EuclideanSpace ℝ (Fin l)))
    (q : ℝ≥0 → Fin m → Fin m → EuclideanSpace ℝ (Fin l) → (Fin m → ℝ) → PA A → ℝ)
    (f : ℝ≥0 → Fin m → EuclideanSpace ℝ (Fin l) → (Fin m → ℝ) → PA A → ℝ)
    (ahat : ℝ≥0 → Fin m → (Fin m → ℝ) → (Fin m → ℝ) → EuclideanSpace ℝ (Fin l)) : Prop :=
  (∀ t ≤ T, ∀ i z, ∀ p ∈ stdSimplex ℝ (Fin m), ahat t i z p ∈ A ∧
    ∀ ν, ∀ a ∈ A, a ≠ ahat t i z p → Hi q f t i z (ahat t i z p) p ν < Hi q f t i z a p ν) ∧
  (∀ i, Measurable fun x : Set.Icc (0 : ℝ≥0) T × (Fin m → ℝ) × stdSimplex ℝ (Fin m) =>
    ahat x.1 i x.2.1 x.2.2) ∧
  (∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 ≤ C₂ ∧ ∀ t ≤ T, ∀ i z z', ∀ p ∈ stdSimplex ℝ (Fin m),
    ∀ p' ∈ stdSimplex ℝ (Fin m),
      ‖ahat t i z p - ahat t i z' p'‖ ≤
        C₁ * seminormE i (z - z') + (C₁ + C₂ * seminormE i z) * eucl (p - p'))

/-- Regularity used but not stated by the paper (disclosed): `q` and `f` are jointly measurable on
`[0, T] × A × S × P(A)` for every `(i, j)`, and `f` is bounded there. -/
def RegularData (T : ℝ≥0) (A : Set (EuclideanSpace ℝ (Fin l)))
    (q : ℝ≥0 → Fin m → Fin m → EuclideanSpace ℝ (Fin l) → (Fin m → ℝ) → PA A → ℝ)
    (f : ℝ≥0 → Fin m → EuclideanSpace ℝ (Fin l) → (Fin m → ℝ) → PA A → ℝ) : Prop :=
  (∀ i j, Measurable fun x : Set.Icc (0 : ℝ≥0) T × A × stdSimplex ℝ (Fin m) × PA A =>
    q x.1 i j x.2.1 x.2.2.1 x.2.2.2) ∧
  (∀ i, Measurable fun x : Set.Icc (0 : ℝ≥0) T × A × stdSimplex ℝ (Fin m) × PA A =>
    f x.1 i x.2.1 x.2.2.1 x.2.2.2) ∧
  ∃ K : ℝ, ∀ t ≤ T, ∀ i, ∀ a ∈ A, ∀ p ∈ stdSimplex ℝ (Fin m), ∀ ν, |f t i a p ν| ≤ K

end

end ExtFSMFG.Existence


