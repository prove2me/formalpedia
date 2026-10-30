-- Prove2me | Definitions.Def_JuschenkoMonod
-- name    : JuschenkoMonod
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T17:15:19.449988+00:00
-- url     : https://prove2.me/theorems/8e8f100a-6cbd-4686-80e0-d3815dae603d
-- title:
--   Piecewise translations, Bernoulli densities, means on finite sets and Cantor systems (Juschenko–Monod 2013)
-- statement:
--   The objects of Juschenko–Monod's paper. Page numbers are those of the Annals of Mathematics.
--
--   **Piecewise translations.** p. 776: "we denote by $W(\mathbf Z)$ the group of all those permutations $g$ of $\mathbf Z$ for which the quantity $|g|_{\rm w} := \sup\{|g(j) - j| : j \in \mathbf Z\}$ is finite."
--   - $W(\mathbf Z)$ is `IntervalExchange.wobbling ℤ`, the permutations $g$ of $\mathbf Z$ with $|g(j) - j|$ bounded.
--   - `wobblingNorm g` is $|g|_{\rm w}$, a supremum of real numbers. Statements use it only for $g \in W(\mathbf Z)$.
--   - `natSet` is $\mathbf N \subseteq \mathbf Z$, the image of the natural numbers, which contains $0$.
--
--   **The Bernoulli space.** p. 777: "We consider $f_n$ as an element of the Hilbert space $L^2(\{0,1\}^{\mathbf Z})$, where $\{0,1\}^{\mathbf Z}$ is endowed with the symmetric Bernoulli measure." p. 783: "It will be convenient to identify the Pontryagin dual of the (discrete) group $\mathscr P_{\rm f}(X)$ with the generalised Bernoulli $G$-shift $\{0,1\}^X$".
--   - $\{0,1\}^X$ is `X → Fin 2`. `bernoulli X` is the product of the uniform probability measures on $\{0, 1\}$.
--   - `l2Norm f` is the $L^2$ norm of $f$ for this measure.
--   - `restrictZero x₀ f` is $f|_{\omega_{x_0}=0}$. In the source's words, p. 783: "$f_n|_{\omega_{x_0}=0}$ denotes the function $f_n$ multiplied by the characteristic function of the cylinder set describing the elementary event $\omega_{x_0} = 0$."
--   - For a group $G$ acting on $X$, the shift is $(g\omega)_x = \omega_{g^{-1}x}$, and $g$ acts on functions by $(gf)(\omega) = f(g^{-1}\omega)$. `translate g f` is this function $gf$, evaluated as $\omega \mapsto f(x \mapsto \omega_{gx})$.
--
--   **The densities $f_n$.** p. 777: "For any $n \in \mathbf N$, we define $$f_n\colon \{0,1\}^{\mathbf Z} \longrightarrow (0,1], \qquad f_n(x) = \exp\Big(-n\sum_{j\in\mathbf Z} x_je^{-|j|/n}\Big),$$ where $x = \{x_j\}_{j\in\mathbf Z} \in \{0,1\}^{\mathbf Z}$." And: "In preparation for the proof, we write $a_{n,j} = \exp(-ne^{-|j|/n})$ for $j \in \mathbf Z$."
--   - `fn n` is $f_n$ and `a n j` is $a_{n,j}$.
--   - `innerRatio g n` is $\langle g(f_n), f_n\rangle/\|f_n\|^2$. The inner product is $\int g(f_n)\,f_n$ for the Bernoulli measure, since $f_n$ is real-valued.
--
--   **The series $F_n$ and the function $B$.** p. 778: "Define the function $F_n\colon W(\mathbf Z) \to \mathbf R$ by the absolutely convergent series: $$F_n(g) = \sum_{j\in\mathbf Z}\frac{a_{n,j}^2}{1 + a_{n,j}^2}\,e^{-|j|/n}\Big(|g(j)| - |j|\Big).$$" p. 781: "Thus let $g \in W(\mathbf Z)$ be given; writing $b_0 = |g(0)|$ and $b_j = \big(|g(j)| - |j|\big) + \big(|g(-j)| - |-j|\big)$ for $j > 0$, …" and "Define functions $B$ and $\psi$ on $\mathbf R_{\ge0}$ by $B(t) = \sum_{0\le j\le t} b_j$".
--   - `F n g` is $F_n(g)$, a sum over $\mathbf Z$.
--   - `b g j` is $b_j$ and `B g t` is $B(t)$, the sum of $b_j$ over the integers $0 \le j \le t$. They are defined for every permutation $g$; the statements use them for $g \in W(\mathbf Z)$.
--
--   **Means on sets of finite subsets.** p. 783: "Let $G$ be a group acting on a set $X$. The collection $\mathscr P_{\rm f}(X)$ of finite subsets of $X$ is an abelian $G$-group for the operation $\triangle$ of symmetric difference. The resulting semidirect product $\mathscr P_{\rm f}(X) \rtimes G$, which can be thought of as the 'lamplighter' restricted wreath product associated to the $G$-action on $X$, has itself a natural 'affine' action on $\mathscr P_{\rm f}(X)$, where the latter set can be considered as the coset space $(\mathscr P_{\rm f}(X) \rtimes G)/G$."
--   - $\mathscr P_{\rm f}(X)$ is `Finset X`, on which $G$ acts by images, $gE = \{gx : x \in E\}$.
--   - In the affine action, $(F, g) \in \mathscr P_{\rm f}(X) \rtimes G$ sends $E$ to $F \mathbin{\triangle} gE$.
--   - A mean on a set $Y$ is a finitely additive probability measure defined on all subsets of $Y$ (`Garrido.IsFinitelyAdditiveMeasure`, total mass $1$).
--   - `IsInvariantMean G m` says that $m$ is a mean on $Y$ invariant under the action of $G$ on $Y$.
--   - `IsLampInvariant G m` says that a function $m$ on sets of finite subsets of $X$ is invariant under the affine action of $\mathscr P_{\rm f}(X) \rtimes G$.
--
--   **The ubiquitous pattern property.** p. 785: "A subgroup $G$ of $W(\mathbf Z)$ has the *ubiquitous pattern property* if for every finite set $F \subseteq G$ and every $n \in \mathbf N$, there exists a constant $k = k(n, F)$ such that for every $j \in \mathbf Z$, there exists $t \in \mathbf Z$ such that $[t-n, t+n] \subseteq [j-k, j+k]$ and such that for every $i \in [-n, n]$ and every $g \in F$, we have $g(i+t) = g(i)+t$."
--   - `HasUbiquitousPatternProperty G` is this property, with $k$ a natural number and the intervals intervals of integers.
--
--   **Cantor systems.** p. 775: "A *Cantor system* $(T, C)$ is a homeomorphism $T$ of the Cantor space $C$; it is called *minimal* if $T$ admits no proper invariant closed subset. The *topological full group* $[[T]]$ of a Cantor system is the group of all homeomorphisms of $C$ that are given piecewise by powers of $T$, each piece being open in $C$."
--   - A Cantor space is a space satisfying `CantorSystems.IsCantorSpace`.
--   - `zAction T` is the action of $\mathbf Z$ by the powers of $T$, $k \cdot x = T^kx$.
--   - `fullGroup T` is $[[T]]$: `CantorSystems.topologicalFullGroup` for this action. Its elements are the homeomorphisms $h$ of $C$ such that every point has a neighbourhood on which $h$ agrees with some power of $T$.
--   - `IsMinimal T` says that every closed set $S$ with $T(S) = S$ is empty or all of $C$.
--   - `IsMinimalAction Γ C` is the same condition for an action of a group $\Gamma$ by homeomorphisms: every closed $\Gamma$-invariant set is empty or all of $C$. It is used for the minimal Cantor $\mathbf Z^2$-systems on p. 776.
--   - `shiftHomeomorph S` is the shift $(\tau x)_i = x_{i+1}$ on a subshift $S$ (a closed shift-invariant set of sequences, `CantorSystems.Subshift`).
--   - `subshiftEntropy S` is the topological entropy of the shift on a subshift $S$ over the alphabet $\{0, \dots, m-1\}$: Mathlib's `Dynamics.coverEntropy` of the whole space, for the uniform structure of the product of discrete alphabets. p. 775: "subshifts can be distinguished by their entropy".
--   - p. 786: "Let $T$ be a homeomorphism of a Cantor space $C$ and choose a point $p \in C$. If $T$ has no finite orbits, then we can define a map $\pi_p\colon [[T]] \longrightarrow W(\mathbf Z)$ by the requirement $g(T^jp) = T^{\pi_p(g)(j)}p$, $(g \in [[T]], j \in \mathbf Z)$." `IsOrbitIndexing T p φ` says that a map $\varphi$ from $[[T]]$ to the permutations of $\mathbf Z$ satisfies this requirement.
--
--   **Amenability.** A group is amenable when it carries a left-invariant finitely additive probability measure defined on all its subsets (`Garrido.IsAmenable`). An action of $H$ on $Y$ "with an invariant mean" (p. 784) is `IntervalExchange.IsAmenableAction H Y`. A group is locally finite when each of its finitely generated subgroups is finite (`Chou.IsLocallyFinite`).
-- source:
--   Juschenko, K. and Monod, N., Cantor systems, piecewise translations and simple amenable groups, Ann. of Math. (2) 178 (2013) 775–787, https://doi.org/10.4007/annals.2013.178.2.7, pp. 775–786, §1 (W(ℤ), |g|_w, topological full groups), §2 (f_n, a_{n,j}, F_n, B), §3 (means on 𝒫_f(X)) and §4 (the ubiquitous pattern property, π_p)

import Mathlib
import Definitions.Def_Garrido_Amenability
import Definitions.Def_CantorSystems

/-!
# Cantor systems, piecewise translations and the Bernoulli densities of Juschenko–Monod

K. Juschenko and N. Monod, *Cantor systems, piecewise translations and simple amenable groups*,
Ann. of Math. 178 (2013) 775–787 (JM). Page numbers are those of the journal.

Conventions:
- `W(ℤ)` is `IntervalExchange.wobbling ℤ`, the permutations `g` of `ℤ` with `|g j - j|` bounded.
- `{0, 1}^X` is `X → Fin 2`, with the product measure of the uniform measures on `Fin 2`.
- A function `f` on `{0, 1}^X` is moved by `g ∈ G` as `(g f)(ω) = f(g⁻¹ ω)`, where
  `(g ω)_x = ω_{g⁻¹ x}`; so `(g f)(ω) = f(x ↦ ω_{g x})`.
- `𝒫_f(X)` is `Finset X`; `G` acts by images, and `(F, g) ∈ 𝒫_f(X) ⋊ G` acts by `E ↦ F ∆ g E`.
- A mean on a set `Y` is a finitely additive probability measure on all subsets of `Y`
  (`Garrido.IsFinitelyAdditiveMeasure`), as in `IntervalExchange.IsAmenableAction`.
- `ℕ ⊆ ℤ` is the range of the cast `ℕ → ℤ`, so it contains `0`.
- A homeomorphism `T` of `C` gives the `ℤ`-action `k +ᵥ x = T^k x`; its topological full group is
  `CantorSystems.topologicalFullGroup` for this action.
-/

namespace JuschenkoMonod

open MeasureTheory
open scoped ENNReal Pointwise

/-! ## Piecewise translations (JM p. 776) -/

/-- JM p. 776: `|g|_w = sup {|g(j) - j| : j ∈ ℤ}`. -/
noncomputable def wobblingNorm (g : Equiv.Perm ℤ) : ℝ :=
  ⨆ j : ℤ, (|g j - j| : ℝ)

/-- The copy `ℕ ⊆ ℤ` of the natural numbers. -/
def natSet : Set ℤ :=
  Set.range ((↑) : ℕ → ℤ)

/-! ## The Bernoulli space and the densities `f_n` (JM pp. 777–778) -/

section Bernoulli

variable (X : Type*)

/-- JM pp. 777, 783: the symmetric Bernoulli measure on `{0, 1}^X`. -/
noncomputable def bernoulli : Measure (X → Fin 2) :=
  Measure.infinitePi fun _ => (PMF.uniformOfFintype (Fin 2)).toMeasure

variable {X}

/-- The `L²` norm of a function on `{0, 1}^X` for the symmetric Bernoulli measure. -/
noncomputable def l2Norm {E : Type*} [NormedAddCommGroup E] (f : (X → Fin 2) → E) : ℝ :=
  (eLpNorm f 2 (bernoulli X)).toReal

/-- JM pp. 777, 783: `f|_{ω_{x₀} = 0}`, the function `f` multiplied by the characteristic function
of the cylinder set `{ω : ω_{x₀} = 0}`. -/
noncomputable def restrictZero {E : Type*} [Zero E] (x₀ : X) (f : (X → Fin 2) → E) : (X → Fin 2) → E :=
  Set.indicator {ω | ω x₀ = 0} f

/-- The action of `G` on functions on `{0, 1}^X` induced by the generalised Bernoulli shift:
`(g f)(ω) = f(g⁻¹ ω)`, that is, `f` evaluated at `x ↦ ω_{g x}`. -/
def translate {G : Type*} [Group G] [MulAction G X] {E : Type*} (g : G) (f : (X → Fin 2) → E) :
    (X → Fin 2) → E :=
  fun ω => f fun x => ω (g • x)

end Bernoulli

/-- JM p. 777: `f_n(x) = exp(-n ∑_{j ∈ ℤ} x_j e^{-|j|/n})` on `{0, 1}^ℤ`. -/
noncomputable def fn (n : ℕ) (x : ℤ → Fin 2) : ℝ :=
  Real.exp (-(n : ℝ) * ∑' j : ℤ, ((x j : ℕ) : ℝ) * Real.exp (-(|j| : ℝ) / n))

/-- JM p. 777: `a_{n,j} = exp(-n e^{-|j|/n})`. -/
noncomputable def a (n : ℕ) (j : ℤ) : ℝ :=
  Real.exp (-(n : ℝ) * Real.exp (-(|j| : ℝ) / n))

/-- JM p. 777: `⟨g(f_n), f_n⟩ / ‖f_n‖²` in `L²({0, 1}^ℤ)`. -/
noncomputable def innerRatio (g : Equiv.Perm ℤ) (n : ℕ) : ℝ :=
  (∫ x, translate g (fn n) x * fn n x ∂bernoulli ℤ) / l2Norm (fn n) ^ 2

/-- JM p. 778: `F_n(g) = ∑_{j ∈ ℤ} a_{n,j}² / (1 + a_{n,j}²) · e^{-|j|/n} (|g(j)| - |j|)`. -/
noncomputable def F (n : ℕ) (g : Equiv.Perm ℤ) : ℝ :=
  ∑' j : ℤ, a n j ^ 2 / (1 + a n j ^ 2) * Real.exp (-(|j| : ℝ) / n) * ((|g j| : ℝ) - |j|)

/-- JM p. 781: `b_0 = |g(0)|` and `b_j = (|g(j)| - |j|) + (|g(-j)| - |-j|)` for `j > 0`. -/
noncomputable def b (g : Equiv.Perm ℤ) (j : ℕ) : ℝ :=
  if j = 0 then |g 0| else ((|g j| : ℝ) - j) + ((|g (-j)| : ℝ) - j)

/-- JM p. 781: `B(t) = ∑_{0 ≤ j ≤ t} b_j` for `t ≥ 0`. -/
noncomputable def B (g : Equiv.Perm ℤ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (⌊t⌋₊ + 1), b g j

/-! ## Invariant means on sets of finite subsets (JM pp. 776, 783) -/

section Means

variable (G : Type*) {Y : Type*} [Group G] [MulAction G Y]

/-- `m` is a `G`-invariant mean on `Y`: a `G`-invariant finitely additive probability measure on all
subsets of `Y`. -/
def IsInvariantMean (m : Set Y → ℝ≥0∞) : Prop :=
  Garrido.IsFinitelyAdditiveMeasure m ∧ m Set.univ = 1 ∧ Garrido.IsInvariant G m

variable {X : Type*} [MulAction G X] [DecidableEq X]

/-- JM p. 783: `m` is invariant under the affine action of the lamplighter `𝒫_f(X) ⋊ G` on
`𝒫_f(X)`, in which `(F, g)` sends `E` to `F ∆ g E`. -/
def IsLampInvariant (m : Set (Finset X) → ℝ≥0∞) : Prop :=
  ∀ (F : Finset X) (g : G) (S : Set (Finset X)), m ((fun E => symmDiff F (g • E)) '' S) = m S

end Means

/-! ## The ubiquitous pattern property (JM p. 785) -/

/-- JM p. 785: `G` has the ubiquitous pattern property: for every finite `F ⊆ G` and `n ∈ ℕ` there
is `k` such that every interval `[j - k, j + k]` contains a translate `[t - n, t + n]` of `[-n, n]`
on which every `g ∈ F` acts as on `[-n, n]`, translated: `g(i + t) = g(i) + t`. -/
def HasUbiquitousPatternProperty (G : Subgroup (Equiv.Perm ℤ)) : Prop :=
  ∀ (F : Finset G) (n : ℕ), ∃ k : ℕ, ∀ j : ℤ, ∃ t : ℤ,
    Set.Icc (t - n) (t + n) ⊆ Set.Icc (j - k) (j + k) ∧
      ∀ i ∈ Set.Icc (-(n : ℤ)) n, ∀ g ∈ F, (g : Equiv.Perm ℤ) (i + t) = (g : Equiv.Perm ℤ) i + t

/-! ## Cantor systems (JM pp. 775, 786) -/

/-- A group action on `C` is minimal: there is no proper invariant closed subset. -/
def IsMinimalAction (Γ C : Type*) [AddGroup Γ] [TopologicalSpace C] [AddAction Γ C] : Prop :=
  ∀ S : Set C, IsClosed S → (∀ γ : Γ, ∀ x ∈ S, γ +ᵥ x ∈ S) → S = ∅ ∨ S = Set.univ

section Cantor

variable {C : Type*} [TopologicalSpace C]

/-- The action of `ℤ` on `C` by the powers of a homeomorphism `T`: `k +ᵥ x = T^k x`. -/
@[reducible] def zAction (T : C ≃ₜ C) : AddAction ℤ C where
  vadd k x := (T ^ k) x
  zero_vadd x := by
    show (T ^ (0 : ℤ)) x = x
    simp
  add_vadd a b x := by
    show (T ^ (a + b)) x = (T ^ a) ((T ^ b) x)
    rw [zpow_add]; rfl

/-- JM p. 775: the topological full group `[[T]]`, the homeomorphisms of `C` given piecewise by
powers of `T`, each piece open. -/
def fullGroup (T : C ≃ₜ C) : Subgroup (C ≃ₜ C) :=
  @CantorSystems.topologicalFullGroup ℤ C _ (zAction T) _

/-- JM p. 775: `T` is minimal: `T` admits no proper invariant closed subset. -/
def IsMinimal (T : C ≃ₜ C) : Prop :=
  ∀ S : Set C, IsClosed S → T '' S = S → S = ∅ ∨ S = Set.univ

/-- JM p. 786: `φ` satisfies the requirement defining `π_p`:
`g(T^j p) = T^{φ(g)(j)} p` for `g ∈ [[T]]` and `j ∈ ℤ`. -/
def IsOrbitIndexing (T : C ≃ₜ C) (p : C) (φ : fullGroup T → Equiv.Perm ℤ) : Prop :=
  ∀ (g : fullGroup T) (j : ℤ), (g : C ≃ₜ C) ((T ^ j) p) = (T ^ (φ g j)) p

end Cantor

/-- The shift `τ`, `(τ x)_i = x_{i+1}`, as a homeomorphism of a subshift. -/
def shiftHomeomorph {A : Type*} [TopologicalSpace A] (S : CantorSystems.Subshift ℤ A) : S ≃ₜ S where
  toFun x := (1 : ℤ) +ᵥ x
  invFun x := (-1 : ℤ) +ᵥ x
  left_inv x := by
    show (-1 : ℤ) +ᵥ ((1 : ℤ) +ᵥ x) = x
    rw [vadd_vadd]; simp
  right_inv x := by
    show (1 : ℤ) +ᵥ ((-1 : ℤ) +ᵥ x) = x
    rw [vadd_vadd]; simp
  continuous_toFun := by
    refine Continuous.subtype_mk (continuous_pi fun δ => ?_) _
    exact (continuous_apply (δ + 1)).comp continuous_subtype_val
  continuous_invFun := by
    refine Continuous.subtype_mk (continuous_pi fun δ => ?_) _
    exact (continuous_apply (δ + -1)).comp continuous_subtype_val

/-- The topological entropy (`Dynamics.coverEntropy`) of the shift on a subshift over the alphabet
`Fin m`, for the uniform structure of the product of discrete uniformities. -/
noncomputable def subshiftEntropy {m : ℕ} (S : CantorSystems.Subshift ℤ (Fin m)) : EReal :=
  letI : UniformSpace (Fin m) := ⊥
  Dynamics.coverEntropy (fun x : S => (1 : ℤ) +ᵥ x) Set.univ

end JuschenkoMonod


