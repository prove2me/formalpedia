-- Prove2me | Definitions.Def_ColemanMandula_Scattering
-- name    : ColemanMandula_Scattering
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-24T04:38:17.333606+00:00
-- url     : https://prove2.me/theorems/08a92bf9-e205-4f86-aa2c-4fe3b9560fa7
-- title:
--   Coleman–Mandula: scattering data and symmetry generators
-- statement:
--   The momentum-space model of the scattering data and of the symmetry generators.
--
--   **Scattering data** (`ScatteringData`). A type `Shell` of mass hyperboloids with injective masses $m_k\ge0$; multiplicities $N_k\ge1$ (states of given momentum on $H_k$); Wigner matrices $W_k(\Lambda,p)\in U(N_k)$ forming a cocycle ($W_k(1,p)=1$, $W_k(\Lambda_1\Lambda_2,p)=W_k(\Lambda_1,\Lambda_2p)W_k(\Lambda_2,p)$), jointly continuous and smooth in $p$; the two-particle T-matrix $T(p,q\to p',q')$ from $H_k\times H_l$ to $H_{k'}\times H_{l'}$, Lorentz covariant:
--   $$T(\Lambda p,\Lambda q\to\Lambda p',\Lambda q')=(W_{k'}(\Lambda,p')\otimes W_{l'}(\Lambda,q'))\,T(p,q\to p',q')\,(W_k(\Lambda,p)\otimes W_l(\Lambda,q))^\dagger$$
--   for $p+q=p'+q'$; and for each pair $(k,l)$ a set of exceptional energies consisting of isolated points.
--
--   **Hypotheses of the paper.** `ParticleFinite`: $\{k : m_k<M\}$ is finite for every $M$ (assumption 2). `ElasticAnalytic`: for all $k,l$ the elastic amplitude $(p,q,p')\mapsto T(p,q\to p',p+q-p')$ coincides on the physical region, away from normal thresholds $s=(m_a+m_b)^2$, with a real-analytic function on an open neighbourhood of that region (assumption 3). `ScatteringOccurs`: $\langle v, T(p,q\to p,q)v\rangle\ne0$ for all $v\ne0$ whenever $s(p,q)$ is not exceptional (assumption 4 in the form used in Lemma 3; equivalent to Eq. (3) by unitarity). A **good pair** is an on-shell pair whose energy is neither exceptional nor a normal threshold.
--
--   **Multiplication operators.** A multiplier is a matrix function $B_k(p)$ on each hyperboloid; $B(p,q)=B(p)\otimes1+1\otimes B(q)$ (Eq. (19)); $M^*=M-\frac{\operatorname{tr}M}{n}1$ is the traceless part. `IsSymMultiplier` ($B\in\mathfrak B_S$): $B$ smooth near each hyperboloid, pointwise Hermitian, and $B(p',q')\,T(p,q\to p',q')=T(p,q\to p',q')\,B(p,q)$ for every momentum-conserving configuration. `Kset k l p q` $=K(p,q)=\{B\in\mathfrak B_S: B^*(p,q)=0\}$ (Eq. (20)). `IsInternalOn`/`IsInternal`: $b(p)$ Hermitian and $b(\Lambda p)W(\Lambda,p)=W(\Lambda,p)b(p)$ for all Lorentz $\Lambda$ (commutation with the Poincaré group).
--
--   **Wave functions and operators.** Wave functions $f_k:\mathbb R^3\to\mathbb C^{N_k}$ of the spatial momentum; test functions are smooth, compactly supported inside the parameter domain, and non-zero on finitely many hyperboloids. Inner product $\langle f,g\rangle=\sum_k\int \langle f_k(v),g_k(v)\rangle\,d^3v/E_k(v)$; `IsHermitianOp`. The Lorentz action $(U(\Lambda)f)_k(v)=W_k(\Lambda,\Lambda^{-1}p)f_k(\Lambda^{-1}p)$, the translation generators $P_a f=(a\cdot p)f$ (`momOp`), the Lorentz generators $M_Xf=-i\frac{d}{d\theta}\big|_0U(e^{\theta X})f$ (`lorentzGen`), multiplication operators (`multOp`), commutators (`comm`), and `IsLocalDiffOp`: on each hyperboloid the operator is a finite-order differential operator $\sum_{j\le N_k}\sum_{\alpha}C_{k,j,\alpha}(v)\,\partial_{\alpha_1}\cdots\partial_{\alpha_j}$ with smooth matrix coefficients, on test functions.
-- source:
--   S. Coleman and J. Mandula, All Possible Symmetries of the S Matrix, Phys. Rev. 159 (1967) 1251-1256, https://doi.org/10.1103/PhysRev.159.1251, Sec. I.A (assumptions 1-5, Eqs. (2)-(5)) and Sec. II (Eqs. (17)-(20))

import Definitions.Def_ColemanMandula_Kinematics

/-!
# Coleman–Mandula (1967): the scattering data and the symmetry generators

A momentum-space model of the objects in Sec. I.A and Sec. II of Coleman–Mandula:

* the one-particle spectrum, organised by mass hyperboloid (all particle types of one mass
  together), each hyperboloid carrying finitely many states of given momentum on which the
  Lorentz group acts through Wigner matrices;
* the two-particle → two-particle block of the T matrix, `S = 1 - i(2π)⁴ δ⁴(P - P') T`
  (Eq. (2)), defined between momentum-conserving configurations;
* the paper's assumptions 2, 3, 4 as predicates on these data;
* multiplication operators `B(p)` (generators commuting with the translations), their
  two-particle extension `B(p) ⊗ 1 + 1 ⊗ B(q)` (Eq. (19)), and the class `𝔅_S`;
* one-particle wave functions in momentum space, the Poincaré action on them, and
  finite-order differential operators on each hyperboloid (the form of the generators
  established in Lemmas 1–2, used as the algebraic recasting of assumption 5 that the
  paper allows in footnote 12).
-/

namespace ColemanMandula

open Matrix
open scoped Kronecker ContDiff

/-- The spectrum and the two-particle scattering data of a Lorentz-invariant theory.

* `Shell` indexes the distinct masses of the one-particle spectrum (each index is a mass
  hyperboloid, grouping all particle types of that mass);
* `mult k` is the number of one-particle states with a given momentum on hyperboloid `k`
  (sum of the spin multiplicities of the particle types of that mass);
* `wigner k Λ p` is the unitary matrix by which the Lorentz transformation `Λ` maps the
  momentum-eigenstate basis at `p` to that at `Λ p` (a continuous cocycle, smooth in `p`);
* `T k l k' l' p q p' q'` is the T-matrix element from the two-particle state with momenta
  `p ∈ shell k`, `q ∈ shell l` to the one with `p' ∈ shell k'`, `q' ∈ shell l'`; it is only
  meaningful when `p + q = p' + q'`;
* `nullS k l` is the set of exceptional energies `s` at which assumption 4 may fail for
  particles on hyperboloids `k, l` ("null pairs"). -/
structure ScatteringData where
  Shell : Type
  mass : Shell → ℝ
  mass_nonneg : ∀ k, 0 ≤ mass k
  mass_injective : Function.Injective mass
  mult : Shell → ℕ
  mult_pos : ∀ k, 0 < mult k
  wigner : (k : Shell) → Matrix (Fin 4) (Fin 4) ℝ → FourVec →
    Matrix (Fin (mult k)) (Fin (mult k)) ℂ
  wigner_unitary : ∀ k Λ p, IsLorentz Λ → p ∈ massShell (mass k) →
    wigner k Λ p ∈ Matrix.unitaryGroup (Fin (mult k)) ℂ
  wigner_one : ∀ k p, p ∈ massShell (mass k) → wigner k 1 p = 1
  wigner_mul : ∀ k Λ₁ Λ₂ p, IsLorentz Λ₁ → IsLorentz Λ₂ → p ∈ massShell (mass k) →
    wigner k (Λ₁ * Λ₂) p = wigner k Λ₁ (Λ₂ *ᵥ p) * wigner k Λ₂ p
  wigner_continuous : ∀ k, ContinuousOn (fun x : Matrix (Fin 4) (Fin 4) ℝ × FourVec =>
    wigner k x.1 x.2) ({Λ | IsLorentz Λ} ×ˢ massShell (mass k))
  wigner_smooth : ∀ k Λ, IsLorentz Λ → ∃ U : Set FourVec, IsOpen U ∧
    massShell (mass k) ⊆ U ∧ ContDiffOn ℝ ∞ (fun p => Matrix.of.symm (wigner k Λ p)) U
  T : (k l k' l' : Shell) → FourVec → FourVec → FourVec → FourVec →
    Matrix (Fin (mult k') × Fin (mult l')) (Fin (mult k) × Fin (mult l)) ℂ
  /-- Lorentz invariance of the S matrix. -/
  T_lorentz : ∀ Λ, IsLorentz Λ → ∀ k l k' l' p q p' q',
    p ∈ massShell (mass k) → q ∈ massShell (mass l) →
    p' ∈ massShell (mass k') → q' ∈ massShell (mass l') → p + q = p' + q' →
    T k l k' l' (Λ *ᵥ p) (Λ *ᵥ q) (Λ *ᵥ p') (Λ *ᵥ q') =
      (wigner k' Λ p' ⊗ₖ wigner l' Λ q') * T k l k' l' p q p' q' *
        (wigner k Λ p ⊗ₖ wigner l Λ q)ᴴ
  nullS : Shell → Shell → Set ℝ
  /-- Every exceptional energy is an isolated point of the exceptional set. -/
  nullS_isolated : ∀ k l, ∀ s ∈ nullS k l, ∃ ε > 0, ∀ s' ∈ nullS k l, |s' - s| < ε → s' = s

namespace ScatteringData

variable (D : ScatteringData)

/-- Assumption 2 (particle finiteness): for every finite `M` there are only finitely many
mass hyperboloids (equivalently, since each carries finitely many states of given momentum,
finitely many particle types) with mass less than `M`. Positivity of the energy is built into
`massShell` and `mass_nonneg`. -/
def ParticleFinite : Prop :=
  ∀ M : ℝ, {k : D.Shell | D.mass k < M}.Finite

/-- The normal thresholds `s = (m_a + m_b)²`. -/
def thresholds : Set ℝ :=
  {s | ∃ a b : D.Shell, s = (D.mass a + D.mass b) ^ 2}

/-- The physical region of elastic scattering `k l → k l`, away from normal thresholds:
triples `(p, q, p')` with `p, p' ∈ shell k`, `q, q' := p + q - p' ∈ shell l`, and
`s = (p + q)²` not a normal threshold. -/
def elasticRegion (k l : D.Shell) : Set (FourVec × FourVec × FourVec) :=
  {x | x.1 ∈ massShell (D.mass k) ∧ x.2.1 ∈ massShell (D.mass l) ∧
    x.2.2 ∈ massShell (D.mass k) ∧ x.1 + x.2.1 - x.2.2 ∈ massShell (D.mass l) ∧
    mandelstamS x.1 x.2.1 ∉ D.thresholds}

/-- Assumption 3 (weak elastic analyticity), in momentum variables: for every pair of
hyperboloids the elastic amplitude `(p, q, p') ↦ T(p, q → p', p + q - p')` agrees on the
physical region (minus normal thresholds) with a real-analytic function defined on an open
neighbourhood of that region. -/
def ElasticAnalytic : Prop :=
  ∀ k l : D.Shell, ∃ U : Set (FourVec × FourVec × FourVec), IsOpen U ∧
    D.elasticRegion k l ⊆ U ∧
    ∃ F : FourVec × FourVec × FourVec →
        (Fin (D.mult k) × Fin (D.mult l) → Fin (D.mult k) × Fin (D.mult l) → ℂ),
      AnalyticOnNhd ℝ F U ∧
      ∀ x ∈ D.elasticRegion k l, D.T k l k l x.1 x.2.1 x.2.2 (x.1 + x.2.1 - x.2.2) = F x

/-- Assumption 4 (occurrence of scattering), in the form in which it enters the proof of
Lemma 3: by unitarity of `S` (optical theorem), `T |p, q⟩ ≠ 0` (Eq. (3)) is equivalent to the
non-vanishing of the forward elastic amplitude `⟨v, T(p, q → p, q) v⟩` for every nonzero
two-particle internal state `v`. It is required except at the exceptional energies
`s ∈ nullS k l`. -/
def ScatteringOccurs : Prop :=
  ∀ k l : D.Shell, ∀ p q, p ∈ massShell (D.mass k) → q ∈ massShell (D.mass l) →
    mandelstamS p q ∉ D.nullS k l →
    ∀ v : Fin (D.mult k) × Fin (D.mult l) → ℂ, v ≠ 0 →
      star v ⬝ᵥ (D.T k l k l p q p q *ᵥ v) ≠ 0

/-- A pair `(p, q)` with `p ∈ shell k`, `q ∈ shell l` is *good* if it is not a null pair
(its energy is not exceptional) and its energy is not a normal threshold. -/
def GoodPair (k l : D.Shell) (p q : FourVec) : Prop :=
  p ∈ massShell (D.mass k) ∧ q ∈ massShell (D.mass l) ∧
    mandelstamS p q ∉ D.nullS k l ∧ mandelstamS p q ∉ D.thresholds

/-- A multiplication operator: on hyperboloid `k` it multiplies the momentum-space wave
function at `p` by the matrix `B k p`. Only the values on the hyperboloid are relevant. -/
abbrev Multiplier := (k : D.Shell) → FourVec → Matrix (Fin (D.mult k)) (Fin (D.mult k)) ℂ

/-- The two-particle extension of a one-particle operator, Eq. (19):
`B(p, q) = B(p) ⊗ 1 + 1 ⊗ B(q)`. -/
def twoPart {m n : ℕ} (Bp : Matrix (Fin m) (Fin m) ℂ) (Bq : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  Bp ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) + (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ Bq

/-- The traceless part `M* = M - (tr M / n) 1` of a square matrix. -/
noncomputable def tracelessPart {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  M - (M.trace / (Fintype.card ι : ℂ)) • (1 : Matrix ι ι ℂ)

/-- The class `𝔅_S`: Hermitian multiplication operators with infinitely differentiable
matrix functions `B(p)` (on a neighbourhood of each hyperboloid) that commute with the
S matrix on two-particle states, i.e. `B(p', q') T(p, q → p', q') = T(p, q → p', q') B(p, q)`
for all momentum-conserving configurations. -/
def IsSymMultiplier (B : D.Multiplier) : Prop :=
  (∀ k, ∃ U : Set FourVec, IsOpen U ∧ massShell (D.mass k) ⊆ U ∧
      ContDiffOn ℝ ∞ (fun p => Matrix.of.symm (B k p)) U) ∧
  (∀ k p, p ∈ massShell (D.mass k) → (B k p).IsHermitian) ∧
  (∀ k l k' l' p q p' q',
    p ∈ massShell (D.mass k) → q ∈ massShell (D.mass l) →
    p' ∈ massShell (D.mass k') → q' ∈ massShell (D.mass l') → p + q = p' + q' →
    twoPart (B k' p') (B l' q') * D.T k l k' l' p q p' q' =
      D.T k l k' l' p q p' q' * twoPart (B k p) (B l q))

/-- `K(p, q)` (Eq. (20)): the elements of `𝔅_S` whose two-particle traceless part vanishes
at `(p, q)`, for `p ∈ shell k`, `q ∈ shell l`. -/
def Kset (k l : D.Shell) (p q : FourVec) : Set D.Multiplier :=
  {B | D.IsSymMultiplier B ∧ tracelessPart (twoPart (B k p) (B l q)) = 0}

/-- A multiplication operator `b` on hyperboloid `k` is an infinitesimal internal symmetry
transformation (Sec. I.A: a symmetry generator commuting with the Poincaré group): `b(p)` is
Hermitian and `b` commutes with every Lorentz transformation, i.e.
`b(Λ p) W_k(Λ, p) = W_k(Λ, p) b(p)` for all `Λ` and all `p` on the hyperboloid.
(Commutation with the translations is automatic for multiplication operators.) -/
def IsInternalOn (k : D.Shell) (b : FourVec → Matrix (Fin (D.mult k)) (Fin (D.mult k)) ℂ) :
    Prop :=
  ∀ p, p ∈ massShell (D.mass k) → (b p).IsHermitian ∧
    ∀ Λ, IsLorentz Λ → b (Λ *ᵥ p) * D.wigner k Λ p = D.wigner k Λ p * b p

/-- A multiplier is an infinitesimal internal symmetry transformation on every hyperboloid. -/
def IsInternal (b : D.Multiplier) : Prop :=
  ∀ k, D.IsInternalOn k (b k)

/-! ### One-particle wave functions and operators -/

/-- One-particle momentum-space wave functions: on hyperboloid `k`, a `ℂ^{mult k}`-valued
function of the spatial momentum `v` (the four-momentum is `onShell (mass k) v`). -/
abbrev WaveFn := (k : D.Shell) → ThreeVec → (Fin (D.mult k) → ℂ)

/-- (Not necessarily linear) operators on wave functions. -/
abbrev Op := D.WaveFn → D.WaveFn

/-- Test wave functions (the set `𝒮`): infinitely differentiable with compact support inside
the parameter domain of each hyperboloid, and nonzero on only finitely many hyperboloids. -/
def IsTestFn (f : D.WaveFn) : Prop :=
  (∀ k, ContDiff ℝ ∞ (f k) ∧ HasCompactSupport (f k) ∧
      tsupport (f k) ⊆ shellDomain (D.mass k)) ∧
  {k | f k ≠ 0}.Finite

/-- The Lorentz-invariant inner product
`⟨f, g⟩ = Σ_k ∫ ⟨f_k(v), g_k(v)⟩ d³v / E_k(v)`. -/
noncomputable def innerProd (f g : D.WaveFn) : ℂ :=
  ∑' k, ∫ v, (star (f k v) ⬝ᵥ g k v) / (energy (D.mass k) v : ℂ)

/-- `A` is Hermitian on test functions: `⟨A f, g⟩ = ⟨f, A g⟩` for all test functions. -/
def IsHermitianOp (A : D.Op) : Prop :=
  ∀ f g, D.IsTestFn f → D.IsTestFn g → D.innerProd (A f) g = D.innerProd f (A g)

/-- The unitary action `U(Λ)` of a Lorentz transformation on wave functions:
`(U(Λ) f)_k(v) = W_k(Λ, Λ⁻¹p) f_k(Λ⁻¹p)` with `p = onShell (mass k) v`. -/
noncomputable def lorentzAct (Λ : Matrix (Fin 4) (Fin 4) ℝ) (f : D.WaveFn) : D.WaveFn :=
  fun k v =>
    D.wigner k Λ (Λ⁻¹ *ᵥ onShell (D.mass k) v) *ᵥ
      f k (spatial (Λ⁻¹ *ᵥ onShell (D.mass k) v))

/-- The generator of translations in the direction `a`: multiplication by `a · p`
(`U(1, t a) = exp(-i t a·P)`). -/
noncomputable def momOp (a : FourVec) : D.Op :=
  fun f k v => ((mdot a (onShell (D.mass k) v) : ℝ) : ℂ) • f k v

/-- The Hermitian generator of the one-parameter Lorentz group `exp(θ X)`:
`(M_X f) = -i d/dθ|_{θ=0} U(exp(θ X)) f`, pointwise. -/
noncomputable def lorentzGen (X : Matrix (Fin 4) (Fin 4) ℝ) : D.Op :=
  fun f k v => (-Complex.I) • deriv (fun θ : ℝ => D.lorentzAct (lorentzExp X θ) f k v) 0

/-- The multiplication operator defined by a multiplier `B`. -/
noncomputable def multOp (B : D.Multiplier) : D.Op :=
  fun f k v => B k (onShell (D.mass k) v) *ᵥ f k v

/-- The commutator `[A, B] = AB - BA` of two operators. -/
def comm (A B : D.Op) : D.Op :=
  fun f => A (B f) - B (A f)

/-- `A` acts, on every hyperboloid, as a differential operator of finite order in the
spatial momentum with infinitely differentiable matrix-valued coefficients:
`(A f)_k(v) = Σ_{j ≤ N_k} Σ_{α ∈ {1,2,3}^j} C_{k,j,α}(v) ∂_{α₁} ⋯ ∂_{α_j} f_k(v)`
for all test functions `f` and all `v` in the parameter domain. In particular `A` does not
connect different hyperboloids. -/
def IsLocalDiffOp (A : D.Op) : Prop :=
  ∃ N : D.Shell → ℕ,
  ∃ C : (k : D.Shell) → (j : ℕ) → (Fin j → Fin 3) → ThreeVec →
      Matrix (Fin (D.mult k)) (Fin (D.mult k)) ℂ,
    (∀ k j α, ContDiffOn ℝ ∞
        (fun v => Matrix.of.symm (C k j α v))
        (shellDomain (D.mass k))) ∧
    ∀ f, D.IsTestFn f → ∀ k, ∀ v ∈ shellDomain (D.mass k),
      A f k v = ∑ j ∈ Finset.range (N k + 1), ∑ α : Fin j → Fin 3,
        C k j α v *ᵥ
          (iteratedFDeriv ℝ j (f k) v (fun i => EuclideanSpace.single (α i) (1 : ℝ)))

end ScatteringData

end ColemanMandula


