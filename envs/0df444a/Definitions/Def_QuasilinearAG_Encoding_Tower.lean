-- Prove2me | Definitions.Def_QuasilinearAG_Encoding_Tower
-- name    : QuasilinearAG_Encoding_Tower
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T15:40:57.415778+00:00
-- url     : https://prove2.me/theorems/c2cfa212-c0f2-461c-a412-b2eee0be0d5d
-- title:
--   Places, divisors, genus and differents; the second Garcia–Stichtenoth tower, Cartier coefficients $C_j$, $u_a=C_0^\kappa(m_a)$ and the divisor $A$ of (3.15)
-- statement:
--   **Function fields.** Let $F$ be a field containing a field $k$.
--
--   - A **place** $P$ of $F/k$ is given by its normalized discrete valuation $\operatorname{ord}_P:F\to\mathbb Z\cup\{\infty\}$: $\operatorname{ord}_P(fg)=\operatorname{ord}_P f+\operatorname{ord}_P g$, $\operatorname{ord}_P(f+g)\ge\min$, value group $\mathbb Z$, and $\operatorname{ord}_P c=0$ for $c\in k^\times$. Its valuation ring is $O_P=\{\operatorname{ord}_P\ge0\}$, its maximal ideal $m_P=\{\operatorname{ord}_P>0\}$, and $\deg P=[O_P/m_P:k]$.
--   - The **ramification index** $e_P$ of $P$ over a subfield $K_0$ is the least positive value of $\operatorname{ord}_P$ on $K_0^\times$. The value $f(P)\in k$ is the constant $c$ with $\operatorname{ord}_P(f-c)>0$. $P$ lies **above** $\beta\in k$ (for an element $s$) when $\operatorname{ord}_P(s-\beta)>0$.
--   - A **divisor** is a function $A$ from places to $\mathbb Z$; $\deg A=\sum_P A(P)\deg P$; $L(A)=\{f:\operatorname{ord}_P f\ge-A(P)\ \forall P\}$, $\ell(A)=\dim_k L(A)$, and the **genus** is $\max_A(\deg A-\ell(A)+1)$ over divisors of finite support.
--   - For a separating $s$ and the derivation $D=d/ds$ ($Ds=1$): $\operatorname{ord}_P(ds)=n$ means $\operatorname{ord}_P(D\pi)=-n$ for a uniformizer $\pi$; the **different exponent** of $P$ over $k(s)$ is $d$ when $\operatorname{ord}_P(D\rho)=\operatorname{ord}_P(D\pi)+d$ for $\rho\in k(s)$ a uniformizer of the place below.
--
--   **The tower (3.1).** For $q>2$ and $h\ge0$, $F$ is the height-$h$ **second Garcia–Stichtenoth tower** over $k$ with coordinates $x_0,\dots,x_h$ when $x_0$ is transcendental over $k$, $L(x_i)=\phi(x_{i-1})$ for $1\le i\le h$, where $L(X)=X^q+X$ and $\phi(X)=X^q/(1+X^{q-1})$, and $F=k(x_0,\dots,x_h)$.
--
--   - $t=x_0^q+x_0$; the **Cartier coefficients** $C_j(f)$ are defined by the unique expansion $f=\sum_{j<q}t^jC_j(f)^q$ (3.3).
--   - The **standard monomials** are $m_a=\prod_{i=1}^h x_i^{a_i}$, $a\in\{0,\dots,q-1\}^h$; $\kappa=\lceil\log_q h\rceil+1$, $Q_*=q^\kappa$, $D=q^h$ (3.2); the **extracted functions** are $u_a=C_0^\kappa(m_a)$ (3.4).
--   - $R_i=k[x_0,t^{-1},x_1,\dots,x_i]$ (§3.1.2); $b<a$ is the lexicographic order comparing the highest tower coordinate first.
--   - $\beta\in k$ is **good** when $\beta^q+\beta\ne0$. $U_\beta[P,a]=u_a(P)$ on the places above $x_0=\beta$ (3.5); it is invertible exactly when $c\mapsto(P\mapsto\sum_a c_a u_a(P))$ is bijective.
--   - $B_0$ is the least effective divisor containing the poles of every $m_a$ at every finite place ($\operatorname{ord}_P x_0\ge0$), and $A=\lfloor B_0/Q_*\rfloor+\sum_{P\text{ finite}}(e_P-1)P+(qD-2)P_\infty$ (3.15), with $e_P$ over $k(x_0)$.
--   - The **exceptional group** $S_{l,h}$ (§A1.2) consists of the places with residues $x_0=\dots=x_{l-1}=0$ and $x_l=\alpha\in C^*$, $C=\ker(X^q+X)\subset k$.
--
--   **Formalization Note** The tower is any field satisfying the defining equations (division in $\phi$ cleared); the paper's degree argument (A1.1) shows each step has degree $q$, so every such field is a model of $F_h$. $C_j(f)$ is $0$ if the expansion (3.3) were not unique (it is, by §3.1.1). $\deg A$ is a finite sum when $A$ has finite support, which each statement asserts. Places over $x_0=\infty$ receive $qD-2$ in $A$; the paper shows there is exactly one.
-- source:
--   Chao, Liu, Li, Ma, Wang, Quasilinear Encoding at the Quadratic Alphabet Scale via Short Cartier Bases, STOC 2027 submission (manuscript sha256 355c15dc…), §3 pp. 7–11 (PDF 9–13), (3.1)–(3.5), (3.15); §A1 pp. 44–46 (PDF 46–48)

import Mathlib

namespace QuasilinearAG.Encoding

/-!
# Places, divisors, genus, and the second Garcia–Stichtenoth tower with its Cartier coefficients

Chao, Liu, Li, Ma, Wang, *Quasilinear Encoding at the Quadratic Alphabet Scale via Short Cartier
Bases*, STOC 2027 submission (manuscript sha256 355c15dc…), §3 pp. 7–11 (PDF 9–13), (3.1)–(3.5),
(3.15); §A1 pp. 44–46 (PDF 46–48).

## Function-field layer (any field `F` over a field `k`)

* `Place k F`: a place, given by its normalized discrete valuation `ord_P : F → ℤ ∪ {∞}`: an
  additive valuation, onto `ℤ` ("ord_P is normalized to have value group ℤ", p. 8), and `0` on
  `k^×`. `Place.integers` is its valuation ring `O_P`, `Place.maxIdeal` the maximal ideal and
  `Place.deg = [O_P/m_P : k]` the residue-field degree ("All divisor degrees count residue-field
  degrees of closed places").
* `Place.ramIdx P K0`: the ramification index of `P` over the place of a subfield `K0` below it:
  the least positive value of `ord_P` on `K0^×` (the value group of the restriction is `e_P ℤ`).
* `Place.evalAt P f`: the value `f(P) ∈ k` of `f` at a place, i.e. the `c ∈ k` with
  `ord_P (f - c) > 0` (for a rational place at which `f` is regular there is exactly one).
* Divisors are functions `Place k F → ℤ`; `divDeg A = Σ_P A(P) deg P` (a finite sum when `A` has
  finite support; statements below assert the finiteness). `rrSpace A = L(A)`, and `genus`
  is Riemann's `max_A (deg A - ℓ(A) + 1)` over divisors of finite support.
* `OrdDiffEq P s n` encodes `ord_P(ds) = n` for a separating element `s`: for the derivation `D`
  of `F` with `D s = 1` (`d/ds`) and a uniformizer `π` at `P`, `ds = dπ / D(π)`, so
  `ord_P(ds) = -ord_P(D π)`.
* `HasDifferentExp P s d`: the different exponent of `P` over `k(s)` is `d`, via
  `d(P | p) = ord_P(dρ/dπ) = ord_P(D ρ) - ord_P(D π)` for `π` a uniformizer at `P`, `ρ ∈ k(s)` a
  uniformizer of the place `p` below (`ord_P ρ = e_P`), `D = d/ds`.

## Tower layer

* `IsGSTower k q h x`: `F` is the height-`h` second Garcia–Stichtenoth tower (3.1) over `k`:
  `x₀` is transcendental over `k`, `L(x_i) = ϕ(x_{i-1})` for `1 ≤ i ≤ h` with `L(X) = X^q + X`,
  `ϕ(X) = X^q/(1 + X^{q-1})` (written without division), and `F = k(x₀, …, x_h)`. Every such `F`
  is a model of the tower `F_h`.
* `towerT q x = t = x₀^q + x₀`; `cartierCoeff q t j f = C_j(f)`, the coefficient in the unique
  expansion `f = Σ_{j<q} t^j C_j(f)^q` (3.3) (`0` if the expansion were not unique);
  `stdMono q h x a = m_a = Π x_i^{a_i}`; `kappaOf q h = κ = ⌈log_q h⌉ + 1` (3.2);
  `extracted q h x a = u_a = C_0^κ(m_a)` (3.4).
* `baseField x = k(x₀)`; `towerRing q x i = R_i = k[x₀, t⁻¹, x₁, …, x_i]` (§3.1.2);
  `colexLT a b`: `a < b` lexicographically, highest tower coordinate compared first.
* `IsGood q β`: `L(β) = β^q + β ≠ 0`. `Place.Above P s β`: `ord_P (s - β) > 0`.
* `finitePoleDivisor s m`: the least effective divisor containing the poles of every `m_a` at
  every finite place (`ord_P s ≥ 0`), `0` at the places over `s = ∞`.
* `shortDivisor q h x = A` of (3.15): `⌊B₀/Q*⌋ + Σ_{P finite}(e_P - 1)P + (qD - 2)P_∞`.
* `exceptionalGroup q x l`: the places with residues `x₀ = ⋯ = x_{l-1} = 0` and
  `x_l = α ∈ C^*`, `C = ker(X^q + X) ⊂ k` (§A1.2, the support of `S_{l,h}`).
* `fibreEvalMap s β u`: `c ↦ (P ↦ Σ_a c_a u_a(P))` on the places above `β`; the matrix `U_β` of
  (3.5) is invertible exactly when this map is bijective.
-/

/-! ## Places and divisors -/

/-- A place of `F/k`, given by its normalized discrete valuation `ord_P` (value group `ℤ`, trivial
on `k^×`). -/
structure Place (k F : Type*) [Field k] [Field F] [Algebra k F] where
  /-- the normalized valuation `ord_P` -/
  v : AddValuation F (WithTop ℤ)
  /-- the value group is `ℤ` -/
  surj : ∀ n : ℤ, ∃ f : F, v f = (n : WithTop ℤ)
  /-- constants are units -/
  const : ∀ c : k, c ≠ 0 → v (algebraMap k F c) = 0

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

namespace Place

/-- The valuation ring `O_P = {f : ord_P f ≥ 0}`. -/
def integers (P : Place k F) : Subalgebra k F where
  carrier := {f | 0 ≤ P.v f}
  mul_mem' {a b} ha hb := by
    show 0 ≤ P.v (a * b)
    rw [P.v.map_mul]
    exact add_nonneg ha hb
  add_mem' {a b} ha hb := le_trans (le_min ha hb) (P.v.map_add a b)
  algebraMap_mem' c := by
    show 0 ≤ P.v (algebraMap k F c)
    by_cases hc : c = 0
    · simp [hc]
    · rw [P.const c hc]

/-- The maximal ideal `m_P = {f : ord_P f > 0}` of `O_P`. -/
def maxIdeal (P : Place k F) : Ideal P.integers where
  carrier := {f | 0 < P.v (f : F)}
  add_mem' {a b} ha hb := lt_of_lt_of_le (lt_min ha hb) (P.v.map_add (a : F) b)
  zero_mem' := by
    show 0 < P.v ((0 : P.integers) : F)
    simp
  smul_mem' c f hf := by
    show 0 < P.v ((c : F) * (f : F))
    rw [P.v.map_mul]
    exact lt_of_lt_of_le hf (le_add_of_nonneg_left c.2)

/-- The degree of a place: `[O_P/m_P : k]`. -/
noncomputable def deg (P : Place k F) : ℕ :=
  Module.finrank k (P.integers ⧸ P.maxIdeal)

/-- The ramification index of `P` over the place of the subfield `K0` below it: the least positive
value of `ord_P` on `K0^×`. -/
noncomputable def ramIdx (P : Place k F) (K0 : IntermediateField k F) : ℕ :=
  sInf {n : ℕ | 0 < n ∧ ∃ g ∈ K0, P.v g = ((n : ℤ) : WithTop ℤ)}

/-- The value `f(P) ∈ k`: the constant `c` with `ord_P (f - c) > 0` (`0` if there is none). -/
noncomputable def evalAt (P : Place k F) (f : F) : k := by
  classical
  exact if h : ∃ c : k, 0 < P.v (f - algebraMap k F c) then h.choose else 0

/-- `P` lies above the value `β` of `s`: `ord_P (s - β) > 0`. -/
def Above (P : Place k F) (s : F) (β : k) : Prop :=
  0 < P.v (s - algebraMap k F β)

end Place

/-- The degree `Σ_P A(P) deg P` of a divisor (a finite sum when `A` has finite support). -/
noncomputable def divDeg (A : Place k F → ℤ) : ℤ :=
  ∑ᶠ P, A P * (P.deg : ℤ)

/-- The Riemann–Roch space `L(A) = {f : ord_P f ≥ -A(P) for every place P}` (with `0`). -/
def rrSpace (A : Place k F → ℤ) : Submodule k F where
  carrier := {f | ∀ P : Place k F, ((-A P : ℤ) : WithTop ℤ) ≤ P.v f}
  add_mem' {a b} ha hb P := le_trans (le_min (ha P) (hb P)) (P.v.map_add a b)
  zero_mem' P := by simp
  smul_mem' c f hf P := by
    show ((-A P : ℤ) : WithTop ℤ) ≤ P.v (c • f)
    rw [Algebra.smul_def, P.v.map_mul]
    by_cases hc : c = 0
    · simp [hc]
    · rw [P.const c hc, zero_add]
      exact hf P

/-- The genus, as in Riemann's theorem: `max (deg A - ℓ(A) + 1)` over divisors `A` of finite
support, `ℓ(A) = dim_k L(A)`. -/
noncomputable def genus (k F : Type*) [Field k] [Field F] [Algebra k F] : ℤ :=
  sSup {g : ℤ | ∃ A : Place k F → ℤ, (Function.support A).Finite ∧
    g = divDeg A - (Module.finrank k (rrSpace A) : ℤ) + 1}

/-- `ord_P(ds) = n`: for the derivation `D = d/ds` (`D s = 1`) and any uniformizer `π` at `P`,
`ord_P (D π) = -n` (since `dπ = D(π) ds` and `ord_P dπ = 0`). -/
def OrdDiffEq (P : Place k F) (s : F) (n : ℤ) : Prop :=
  ∀ D : Derivation k F F, D s = 1 → ∀ π : F, P.v π = ((1 : ℤ) : WithTop ℤ) →
    P.v (D π) = ((-n : ℤ) : WithTop ℤ)

/-- The different exponent of `P` over `k(s)` is `d`: `ord_P(D ρ) = ord_P(D π) + d` for
`D = d/ds`, `π` a uniformizer at `P` and `ρ ∈ k(s)` a uniformizer of the place below. -/
def HasDifferentExp (P : Place k F) (s : F) (d : ℤ) : Prop :=
  ∀ D : Derivation k F F, D s = 1 → ∀ π ρ : F, P.v π = ((1 : ℤ) : WithTop ℤ) →
    ρ ∈ IntermediateField.adjoin k {s} →
    P.v ρ = (((P.ramIdx (IntermediateField.adjoin k {s}) : ℕ) : ℤ) : WithTop ℤ) →
    P.v (D ρ) = P.v (D π) + ((d : ℤ) : WithTop ℤ)

/-- The least effective divisor containing the poles of every `m a` at every finite place
(`ord_P s ≥ 0`); it is `0` at the places over `s = ∞`. -/
noncomputable def finitePoleDivisor {ι : Type*} [Fintype ι] (s : F) (m : ι → F) :
    Place k F → ℤ := fun P =>
  if 0 ≤ P.v s then
    ((Finset.univ.sup fun a => (-((P.v (m a)).untopD 0)).toNat : ℕ) : ℤ)
  else 0

/-- The evaluation map `c ↦ (P ↦ Σ_a c_a u_a(P))` on the places above `β`: the matrix `U_β`. -/
noncomputable def fibreEvalMap {ι : Type*} [Fintype ι] (s : F) (β : k) (u : ι → F) :
    (ι → k) → ({P : Place k F // P.Above s β} → k) :=
  fun c P => ∑ a, c a * P.1.evalAt (u a)

/-! ## The second Garcia–Stichtenoth tower -/

/-- `F` is the height-`h` second Garcia–Stichtenoth tower over `k` with coordinates `x 0, …, x h`:
`x₀` transcendental, `x_i^q + x_i = x_{i-1}^q / (1 + x_{i-1}^{q-1})` for `1 ≤ i ≤ h`, and
`F = k(x₀, …, x_h)`. -/
structure IsGSTower (k : Type*) [Field k] {F : Type*} [Field F] [Algebra k F] (q h : ℕ)
    (x : ℕ → F) : Prop where
  transcendental : Transcendental k (x 0)
  eqn : ∀ i, 1 ≤ i → i ≤ h → (x i ^ q + x i) * (1 + x (i - 1) ^ (q - 1)) = x (i - 1) ^ q
  generates : IntermediateField.adjoin k (x '' Set.Iic h) = ⊤

/-- The separating element `t = x₀^q + x₀`. -/
def towerT (q : ℕ) (x : ℕ → F) : F := x 0 ^ q + x 0

/-- The Cartier coefficient `C_j(f)`: `f = Σ_{j<q} t^j C_j(f)^q` (3.3) (`0` if this expansion did
not exist uniquely, or `j ≥ q`). -/
noncomputable def cartierCoeff (q : ℕ) (t : F) (j : ℕ) (f : F) : F := by
  classical
  exact if h : ∃! g : Fin q → F, f = ∑ i : Fin q, t ^ (i : ℕ) * g i ^ q then
    (if hj : j < q then h.exists.choose ⟨j, hj⟩ else 0) else 0

/-- The standard monomial `m_a = Π_{i=1}^h x_i^{a_i}`, `a ∈ {0, …, q-1}^h` (`a i` is `a_{i+1}`). -/
def stdMono (q h : ℕ) (x : ℕ → F) (a : Fin h → Fin q) : F :=
  ∏ i : Fin h, x ((i : ℕ) + 1) ^ ((a i : ℕ))

/-- `κ = ⌈log_q h⌉ + 1` (3.2). -/
def kappaOf (q h : ℕ) : ℕ := Nat.clog q h + 1

/-- The extracted function `u_a = C_0^κ(m_a)` (3.4). -/
noncomputable def extracted (q h : ℕ) (x : ℕ → F) (a : Fin h → Fin q) : F :=
  (cartierCoeff q (towerT q x) 0)^[kappaOf q h] (stdMono q h x a)

/-- The rational function field `k(x₀)` inside `F`. -/
def baseField (x : ℕ → F) : IntermediateField k F :=
  IntermediateField.adjoin k {x 0}

/-- The localized ring `R_i = k[x₀, t⁻¹, x₁, …, x_i]` (§3.1.2). -/
def towerRing (q : ℕ) (x : ℕ → F) (i : ℕ) : Subalgebra k F :=
  Algebra.adjoin k ({x 0, (towerT q x)⁻¹} ∪ x '' Set.Icc 1 i)

/-- `b < a` in the lexicographic order with the highest tower coordinate compared first. -/
def colexLT {h q : ℕ} (b a : Fin h → Fin q) : Prop :=
  ∃ i : Fin h, b i < a i ∧ ∀ j : Fin h, i < j → b j = a j

/-- A base value `β ∈ k` is good when `L(β) = β^q + β ≠ 0`. -/
def IsGood (q : ℕ) (β : k) : Prop := β ^ q + β ≠ 0

/-- The divisor `A = ⌊B₀/Q*⌋ + Σ_{P finite}(e_P - 1)P + (qD - 2)P_∞` of (3.15), with `B₀` the
common effective finite pole divisor of the standard monomials, `Q* = q^κ`, `D = q^h`, `e_P` the
ramification index over `k(x₀)`; places over `x₀ = ∞` get `qD - 2`. -/
noncomputable def shortDivisor (q h : ℕ) (x : ℕ → F) : Place k F → ℤ := fun P =>
  if 0 ≤ P.v (x 0) then
    finitePoleDivisor (x 0) (stdMono q h x) P / ((q : ℤ) ^ kappaOf q h)
      + ((P.ramIdx (baseField x) : ℤ) - 1)
  else (q : ℤ) * (q : ℤ) ^ h - 2

/-- The places of the exceptional group `S_{l,h}` (§A1.2): residues `x₀ = ⋯ = x_{l-1} = 0` and
`x_l = α` for some `α ∈ C^*`, `C = ker(X^q + X : k → k)`. -/
def exceptionalGroup (q : ℕ) (x : ℕ → F) (l : ℕ) : Set (Place k F) :=
  {P | (∀ i < l, 0 < P.v (x i)) ∧
    ∃ α : k, α ≠ 0 ∧ α ^ q + α = 0 ∧ 0 < P.v (x l - algebraMap k F α)}

end QuasilinearAG.Encoding


