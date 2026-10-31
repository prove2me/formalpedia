-- Prove2me | Definitions.Def_EdgeworthCore_Model
-- name    : EdgeworthCore_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:13:57.46141+00:00
-- url     : https://prove2.me/theorems/c2cb0671-88c6-43fd-a3e4-84e25654e6de
-- title:
--   Exchange economies, allocations, coalitions that block, the $\kappa$-core, replica economies $\mathcal E^n$, $\varepsilon$-Walrasian equilibrium and the standing assumptions of §2
-- statement:
--   This module sets up the model of §2 of Barman and Echenique. Throughout, $\ell$ is the number of goods, bundles are vectors in $\mathbb R^\ell$ with the Euclidean norm $\|\cdot\|$, and $x\le y$ is meant coordinatewise. We write $\mathbb R^\ell_+=\{x: x_a\ge 0\text{ for all }a\}$, $\Delta=\{p\in\mathbb R^\ell_+ : \sum_a p_a=1\}$ for the standard simplex, $\mathbf 1$ for the all-ones vector and $p^{\mathsf T}x=\sum_a p_a x_a$.
--
--   1. **Exchange economy.** $\mathcal E=((u_i,\omega_i))_{i\in I}$: each consumer $i$ of a finite set $I$ has a utility function $u_i$ on bundles (only its values on $\mathbb R^\ell_+$ matter) and an endowment $\omega_i\in\mathbb R^\ell_+$. For the paper's economy $I=[h]$.
--   2. **Allocation.** A family $x=(x_i)_{i\in I}$ with every $x_i\in\mathbb R^\ell_+$ and $\sum_i x_i=\sum_i\omega_i$.
--   3. **$S$-allocation and blocking.** For a coalition (a nonempty set) $S\subseteq I$, an $S$-allocation is a family $(y_i)_{i\in S}$ of bundles in $\mathbb R^\ell_+$ with $\sum_{i\in S}y_i=\sum_{i\in S}\omega_i$. The coalition $S$ *blocks* $x$ if some $S$-allocation has $u_i(y_i)>u_i(x_i)$ for every $i\in S$.
--   4. **$\kappa$-core.** For $\kappa\in\mathbb Z_+$, the allocations of $\mathcal E$ that no coalition of cardinality at most $\kappa$ blocks.
--   5. **Replica economy.** For $n\in\mathbb N$, $\mathcal E^n$ has the consumers $(i,t)$, $i\in[n]$, $t\in[h]$, with $u_{i,t}=u_t$ and $\omega_{i,t}=\omega_t$. The $n$-times replicated version of an allocation $x=(x_t)_{t\in[h]}$ of $\mathcal E$ gives $x_t$ to every consumer $(i,t)$.
--   6. **Equal treatment.** An allocation $X=(X_{i,t})$ of $\mathcal E^n$ has the equal treatment property if $X_{i,t}=X_{i',t}$ for every type $t$ and all $i,i'\in[n]$.
--   7. **$\varepsilon$-Walrasian equilibrium.** A pair $(p,x)$ with $p\in\Delta$ and $x$ an allocation of $\mathcal E$ such that, for every consumer $i$, (i) $|p^{\mathsf T}x_i-p^{\mathsf T}\omega_i|\le\varepsilon$, and (ii) every bundle $y\in\mathbb R^\ell_+$ with $u_i(y)>u_i(x_i)$ satisfies $p^{\mathsf T}y>p^{\mathsf T}\omega_i-\varepsilon/h$, where $h=|I|$. An allocation $x$ is $\varepsilon$-Walrasian if such a $p$ exists.
--   8. **Strict monotonicity.** For $x,y\in\mathbb R^\ell_+$ with $x\le y$ and $x\ne y$, $u(x)<u(y)$.
--   9. **Standing assumptions** with parameters $\alpha,\lambda,r,\varepsilon$: every $u_i$ is continuously differentiable, strictly monotonic and concave on $\mathbb R^\ell_+$ and $\lambda$-Lipschitz there for the Euclidean norm ($\lambda\ge 0$); $\alpha>0$, $r\ge 0$, and every $u_i$ is $\alpha$-strongly concave on the ball of radius $r$ about its endowment,
--   $$u_i(y)\le u_i(x)+\nabla u_i(x)^{\mathsf T}(y-x)-\frac{\alpha}{2}\|y-x\|^2\qquad\text{for all }x,y\in\mathbb R^\ell_+\text{ with }\|x-\omega_i\|,\|y-\omega_i\|\le r;$$
--   the radius satisfies $\alpha r^2\ge 2\varepsilon\lambda\ell/h+2$; and utilities are normalized on allocations of $\mathcal E$: $u_i(x_i)\in[0,1)$ for every allocation $x$ of $\mathcal E$ and every $i$.
--   10. **Trade sets.** For an allocation $y$ and a margin $\eta$, $Q_i^\eta=\{z\in\mathbb R^\ell : u_i(z+\omega_i)\ge u_i(y_i)+\eta\}$, where membership includes $z+\omega_i\in\mathbb R^\ell_+$ (the paper's $Q_i^\eta$ of §3.1 and $P_i^\eta$ of §3.2).
--
--   These are the objects of every statement of the mission: the $\kappa$-core of the replica economy is the hypothesis of the main theorem and the $\varepsilon$-Walrasian equilibrium its conclusion.
--
--   **Formalization Note** Bundles are `EuclideanSpace ℝ (Fin ℓ)`. Utilities are total functions on $\mathbb R^\ell$, and every hypothesis on them refers only to $\mathbb R^\ell_+$; gradients are derivatives within $\mathbb R^\ell_+$, which coincide with the usual gradient at interior points. Strong concavity is assumed on each ball intersected with $\mathbb R^\ell_+$ only, not on all of $\mathbb R^\ell_+$ (which would contradict monotonicity). The consumers of $\mathcal E^n$ are pairs $(i,t)$ in `Fin n × Fin h`, so the same definitions of allocation, blocking and core serve $\mathcal E$ and $\mathcal E^n$.
-- source:
--   Barman–Echenique, The Edgeworth Conjecture with Small Coalitions and Approximate Equilibria in Large Economies, arXiv:1905.05165v1, §2, pp.5–8 (Notational Conventions, Exchange economies, strong concavity and αr² ≥ 2ελℓ/h + 2 p.5; Core p.5–6; ε-Walrasian equilibrium p.6; Utility normalization, Replica Economies, equal treatment p.7); §3.1 Q_i^η p.9; §3.2 P_i^η p.12

import Mathlib

open scoped BigOperators

namespace EdgeworthCore

/-- **Commodity space** `ℝ^ℓ` (Barman–Echenique, arXiv:1905.05165v1, §2, p.5).

**Formalization Note.** Bundles and price vectors live in `EuclideanSpace ℝ (Fin ℓ)`, so that
`‖·‖` is the Euclidean norm the paper uses throughout ("`‖·‖` denotes the Euclidean norm", p.5);
`Fin ℓ → ℝ` would carry the sup norm. -/
abbrev Bundle (ℓ : ℕ) := EuclideanSpace ℝ (Fin ℓ)

/-- **The nonnegative orthant** `ℝ^ℓ_+ = {x | x_a ≥ 0 for all a}` (§2, p.5). -/
def orthant (ℓ : ℕ) : Set (Bundle ℓ) := {x | ∀ a, 0 ≤ x a}

/-- **The standard simplex** `Δ := {x ∈ ℝ^ℓ | ∑_a x_a = 1 and x_a ≥ 0 for all a}`
(§2, Notational Conventions, p.5). -/
def simplex (ℓ : ℕ) : Set (Bundle ℓ) := {p | (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1}

/-- **The all-ones vector** `1 ∈ ℝ^ℓ` (§2, p.5). -/
noncomputable def ones (ℓ : ℕ) : Bundle ℓ := (EuclideanSpace.equiv (Fin ℓ) ℝ).symm (fun _ => 1)

/-- **Value of a bundle at prices**, `pᵀx = ∑_a p_a x_a` (§2, p.6). -/
def value {ℓ : ℕ} (p x : Bundle ℓ) : ℝ := ∑ a, p a * x a

/-- **Exchange economy** `E = ((u_i, ω_i))_{i ∈ I}` (§2, Exchange economies, p.5): consumer `i` has
a utility function `u_i` over bundles and an endowment `ω_i ∈ ℝ^ℓ_+`.

**Formalization Note.** The paper's consumers are `[h]`; the index type `ι` is arbitrary so that the
same structure describes `E` (index `Fin h`) and its replica `E^n` (index `Fin n × Fin h`). The
utility is a total function on `ℝ^ℓ`; only its values on `ℝ^ℓ_+` (the paper's domain
`u_i : ℝ^ℓ_+ → ℝ`) enter any definition or hypothesis of this mission. -/
structure Economy (ι : Type*) (ℓ : ℕ) where
  /-- utility function of consumer `i` -/
  u : ι → Bundle ℓ → ℝ
  /-- endowment of consumer `i` -/
  ω : ι → Bundle ℓ
  /-- endowments lie in `ℝ^ℓ_+` -/
  ω_mem : ∀ i, ω i ∈ orthant ℓ

/-- **Allocation** (§2, Core, p.5): `x = (x_i)_i` with every `x_i ∈ ℝ^ℓ_+` and
`∑_i x_i = ∑_i ω_i`. -/
def IsAllocation {ι : Type*} [Fintype ι] {ℓ : ℕ} (E : Economy ι ℓ) (x : ι → Bundle ℓ) : Prop :=
  (∀ i, x i ∈ orthant ℓ) ∧ ∑ i, x i = ∑ i, E.ω i

/-- **S-allocation** (§2, Core, p.6): for a coalition `S`, a family `(y_i)_{i∈S}` with
`∑_{i∈S} y_i = ∑_{i∈S} ω_i`.

**Formalization Note.** The family is given as a function on all consumers; only its values on `S`
matter. Each `y_i`, `i ∈ S`, is required to lie in `ℝ^ℓ_+`, the domain of `u_i` (p.5); the page
does not repeat this, but `u_i(y_i)` is only defined there. -/
def IsSAllocation {ι : Type*} {ℓ : ℕ} (E : Economy ι ℓ) (S : Finset ι) (y : ι → Bundle ℓ) :
    Prop :=
  (∀ i ∈ S, y i ∈ orthant ℓ) ∧ ∑ i ∈ S, y i = ∑ i ∈ S, E.ω i

/-- **Blocking** (§2, Core, p.6): a coalition (a nonempty set of consumers) `S` blocks `x` if there
is an S-allocation `(y_i)_{i∈S}` with `u_i(y_i) > u_i(x_i)` for all `i ∈ S`. (The page writes
`u(x_i)` for `u_i(x_i)`, a typo.) -/
def Blocks {ι : Type*} {ℓ : ℕ} (E : Economy ι ℓ) (S : Finset ι) (x : ι → Bundle ℓ) : Prop :=
  S.Nonempty ∧ ∃ y : ι → Bundle ℓ, IsSAllocation E S y ∧ ∀ i ∈ S, E.u i (x i) < E.u i (y i)

/-- **κ-core** (§2, Core, p.6): the allocations of `E` not blocked by any coalition of cardinality
at most `κ`, `κ ∈ ℤ_+`. -/
def InKappaCore {ι : Type*} [Fintype ι] {ℓ : ℕ} (E : Economy ι ℓ) (κ : ℕ) (x : ι → Bundle ℓ) :
    Prop :=
  IsAllocation E x ∧ ∀ S : Finset ι, S.card ≤ κ → ¬ Blocks E S x

/-- **The n-th replica economy** `E^n` (§2, Replica Economies, p.7): consumers `(i, t)` with
`i ∈ [n]` and type `t`, and `u_{i,t} = u_t`, `ω_{i,t} = ω_t`.

**Formalization Note.** Consumer `(i, t)` is the pair `(i, t) : Fin n × ι`; the copy index is
0-based. -/
def replica {ι : Type*} {ℓ : ℕ} (E : Economy ι ℓ) (n : ℕ) : Economy (Fin n × ι) ℓ where
  u := fun c => E.u c.2
  ω := fun c => E.ω c.2
  ω_mem := fun c => E.ω_mem c.2

/-- **The n-times replicated allocation** (p.8 and footnote 10): consumer `(i, t)` of `E^n`
receives `x_t`. This is how the paper reads "`x ∈ ℝ^{hℓ}_+` belongs to the κ-core of `E^n`"
(pp.7–8). -/
def replicate {ι : Type*} {ℓ : ℕ} (n : ℕ) (x : ι → Bundle ℓ) : Fin n × ι → Bundle ℓ :=
  fun c => x c.2

/-- **Equal treatment property** (§2, p.7): an allocation `X = (X_{i,t})` of `E^n` gives all
consumers of the same type identical bundles, `X_{i,t} = X_{i',t}` for all `t` and `i, i' ∈ [n]`. -/
def EqualTreatment {ι : Type*} {ℓ n : ℕ} (X : Fin n × ι → Bundle ℓ) : Prop :=
  ∀ t : ι, ∀ i i' : Fin n, X (i, t) = X (i', t)

/-- **ε-Walrasian equilibrium** (§2, Equilibrium and approximate equilibrium, p.6): a pair `(p, x)`
with `p ∈ Δ` and `x` an allocation of `E` such that for every consumer `i`:

1. `|pᵀx_i − pᵀω_i| ≤ ε`, and
2. for any bundle `y ∈ ℝ^ℓ_+` with `u_i(y) > u_i(x_i)`, `pᵀy > pᵀω_i − ε/h`,

where `h` is the number of consumers of `E`.

`x` is an **ε-Walrasian allocation** (p.7) if some `p ∈ Δ` makes `(p, x)` an ε-Walrasian
equilibrium. -/
def IsEpsWalrasianEq {ι : Type*} [Fintype ι] {ℓ : ℕ} (E : Economy ι ℓ) (ε : ℝ)
    (p : Bundle ℓ) (x : ι → Bundle ℓ) : Prop :=
  p ∈ simplex ℓ ∧ IsAllocation E x ∧
    ∀ i, |value p (x i) - value p (E.ω i)| ≤ ε ∧
      ∀ y ∈ orthant ℓ, E.u i (x i) < E.u i y →
        value p (E.ω i) - ε / (Fintype.card ι : ℝ) < value p y

/-- **Strict monotonicity on `ℝ^ℓ_+`** (§2, p.5; footnote 8, p.7): for `x, y ∈ ℝ^ℓ_+` with
`x ≤ y` coordinatewise and `x ≠ y`, `u(x) < u(y)`. -/
def StrictlyMonotone {ℓ : ℕ} (u : Bundle ℓ → ℝ) : Prop :=
  ∀ x ∈ orthant ℓ, ∀ y ∈ orthant ℓ, (∀ a, x a ≤ y a) → x ≠ y → u x < u y

/-- **Standing assumptions of §2** (pp.5–7) on an economy `E` with consumers `ι`
(`h = |ι|`) and ℓ goods, with strong-concavity modulus `α`, Lipschitz constant `λ`
(`lam`), strong-concavity radius `r` and approximation parameter `ε`:

1. each `u_i` is continuously differentiable on `ℝ^ℓ_+` (p.5);
2. each `u_i` is strictly monotonic on `ℝ^ℓ_+` (p.5, "monotone increasing"; Theorem 3.2);
3. each `u_i` is concave on `ℝ^ℓ_+` (p.5, "if `α = 0`, then `u` is simply a concave function";
   used on all of `ℝ^ℓ_+` on p.9 and in footnote 12);
4. each `u_i` is `λ`-Lipschitz on `ℝ^ℓ_+` for the Euclidean norm, `λ ≥ 0` common to all `i`
   (p.7, "we will use `λ` to denote the Lipschitz constant of the utility functions");
5. `α > 0`, `r ≥ 0`, and each `u_i` is `α`-strongly concave on the Euclidean ball of radius `r`
   centred at `ω_i` (p.5): for all `x, y` in that ball (and in `ℝ^ℓ_+`),
   `u_i(y) ≤ u_i(x) + ∇u_i(x)ᵀ(y − x) − (α/2)‖y − x‖²`;
6. `αr² ≥ 2ελℓ/h + 2` (p.5);
7. utilities are normalized on allocations of `E` (p.7): `u_i(x_i) ∈ [0, 1)` for every
   allocation `x` of `E` and every `i`.

**Formalization Note.** Gradients are derivatives *within* `ℝ^ℓ_+` (`fderivWithin`), since `u_i`
is only defined there (p.5); the orthant has unique derivatives, so this is the ordinary gradient
in the interior and the one-sided one on the boundary. `∇u(x)ᵀv` is the derivative applied to `v`.
Strong concavity is assumed only on each ball `closedBall ω_i r ∩ ℝ^ℓ_+`, not on all of `ℝ^ℓ_+`:
the paper's region `R` is any set containing these balls (p.5), and global strong concavity is
incompatible with monotonicity. The normalization is the paper's first form `[0, 1)` on allocations
of `E` only (p.7: "the utilities are normalized only for feasible allocations in the underlying
exchange economy"). -/
structure StandingAssumptions {ι : Type*} [Fintype ι] {ℓ : ℕ} (E : Economy ι ℓ)
    (α lam r ε : ℝ) : Prop where
  contDiff : ∀ i, ContDiffOn ℝ 1 (E.u i) (orthant ℓ)
  strictMono : ∀ i, StrictlyMonotone (E.u i)
  concave : ∀ i, ConcaveOn ℝ (orthant ℓ) (E.u i)
  lam_nonneg : 0 ≤ lam
  lipschitz : ∀ i, ∀ x ∈ orthant ℓ, ∀ y ∈ orthant ℓ, |E.u i x - E.u i y| ≤ lam * ‖x - y‖
  alpha_pos : 0 < α
  r_nonneg : 0 ≤ r
  strongConcave : ∀ i, ∀ x ∈ Metric.closedBall (E.ω i) r ∩ orthant ℓ,
    ∀ y ∈ Metric.closedBall (E.ω i) r ∩ orthant ℓ,
      E.u i y ≤ E.u i x + fderivWithin ℝ (E.u i) (orthant ℓ) x (y - x) - α / 2 * ‖y - x‖ ^ 2
  radius : 2 * ε * lam * (ℓ : ℝ) / (Fintype.card ι : ℝ) + 2 ≤ α * r ^ 2
  normalized : ∀ x : ι → Bundle ℓ, IsAllocation E x → ∀ i, 0 ≤ E.u i (x i) ∧ E.u i (x i) < 1

/-- **Trade sets** `Q_i^η` (§3.1, p.9) and `P_i^η` (§3.2, p.12): for a reference allocation `y`,
the trades `z` from the endowment that make consumer `i` better off by at least `η`,
`{z ∈ ℝ^ℓ | u_i(z + ω_i) ≥ u_i(y_i) + η}`.

**Formalization Note.** `z ∈ Q_i^η` iff `z + ω_i ∈ V_i^η ⊆ ℝ^ℓ_+` (p.9; footnote 11, p.10:
"`z_i ≥ −ω_i`"), so membership includes `z + ω_i ∈ ℝ^ℓ_+`. -/
def tradeSet {ι : Type*} {ℓ : ℕ} (E : Economy ι ℓ) (y : ι → Bundle ℓ) (η : ℝ) (i : ι) :
    Set (Bundle ℓ) :=
  {z | z + E.ω i ∈ orthant ℓ ∧ E.u i (y i) + η ≤ E.u i (z + E.ω i)}

end EdgeworthCore


