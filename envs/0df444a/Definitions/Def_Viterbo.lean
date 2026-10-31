-- Prove2me | Definitions.Def_Viterbo
-- name    : Viterbo
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T07:20:37.776632+00:00
-- url     : https://prove2.me/theorems/d7daaf1c-4bb5-40e5-b971-b7960d92b85d
-- title:
--   Symplectic capacities, Viterbo's conjecture, Minkowski billiards and the EHZ capacity (Haim-Kislev–Ostrover 2026)
-- statement:
--   The objects of Haim-Kislev–Ostrover's paper. Page numbers are those of arXiv:2405.16513v3. Phase space $\mathbb R^{2n}$ is `OAI.SymmetricPolar.Phase n`, pairs $z = (q, p)$ of vectors of $\mathbb R^n$ (`Position n`, Euclidean); volume is the product of the Lebesgue measures of the two factors. The published bundle [`SymmetricPolar`](https://prove2.me/theorems/8baa3748-2e8d-413d-8c0b-9b8ac5e1acea) supplies the symplectic form $\omega_0((q, p), (q', p')) = \langle q, p'\rangle - \langle q', p\rangle$, symplectic embeddings (`HasSymplecticEmbedding`: a smooth topological embedding preserving $\omega_0$), the open ball `capacityBall n c` $= \{\pi(|q|^2 + |p|^2) < c\}$ of capacity $c$, and the Gromov width `gromovWidth`. The paper writes $\omega_{\rm std} = \sum dp_i \wedge dq_i = -\omega_0$; a map preserves one exactly when it preserves the other.
--
--   **Capacities and the conjecture.** p. 2: "Definition 1.1. A symplectic capacity is a map $c$ that assigns a non-negative number to each subset $U \subset \mathbb R^{2n}$, and satisfies the following: 1. (Monotonicity) $c(U) \le c(V)$ if there is a symplectic embedding $U \hookrightarrow V$. 2. (Conformality) $c(\alpha U) = \alpha^2 c(U)$, for every $\alpha \in \mathbb R_+$. 3. (Normalization) $c(B^{2n}(1)) = c(Z^{2n}(1)) = \pi$." And: "Here $B^{2n}(r) \subset \mathbb C^n$ is the Euclidean ball of radius $r$, and $Z^{2n}(r)$ is the cylinder $B^2(r) \times \mathbb C^{n-1}$."
--   - `IsSymplecticCapacity n c` is Definition 1.1, for $c$ valued in $[0, \infty]$: the paper's own examples $c_G$ and $c_Z$ take the value $\infty$ (on all of $\mathbb R^{2n}$, and on sets admitting no embedding into a cylinder).
--   - The balls are open: $B^{2n}(1)$ is `capacityBall n π`. `capacityCylinder n c` is $Z^{2n}(r)$ with $\pi r^2 = c$, the points with $\pi(q_1^2 + p_1^2) < c$ (the first coordinate of $\mathbb C^n$ is $q_1 + ip_1$).
--   - p. 2: "and the cylindrical capacity $c_Z(U) = \inf\{\pi r^2 : \exists\, U \overset{s}{\hookrightarrow} Z^{2n}(r)\}$." This is `cylindricalCapacity`.
--   - p. 2: "Throughout this text, the term convex domain refers to a bounded convex set with nonempty interior." This is `IsConvexDomain`.
--   - p. 2: "Conjecture 1.2 (Viterbo, 2000). For any symplectic capacity $c$ and any convex domain $K \subset \mathbb R^{2n}$, $c(K)^n \le n!\,\mathrm{Vol}(K)$." This is `ViterboConjecture n`.
--   - `IsSymplectomorphic U V` says that a symplectic embedding of $U$ has image $V$.
--
--   **The Ekeland–Hofer–Zehnder capacity.** p. 2: "for the class of convex domains it is known that, among others, the Hofer–Zehnder capacity, the first Ekeland–Hofer capacity, and the symplectic homology capacity coincide, and are equal to the minimal action among closed characteristics (or closed Reeb orbits) on the boundary", with footnote 1: "Without the smoothness assumption, one needs to consider 'generalized' closed characteristics on the boundary (see, e.g., §2.3 in [10])." Then: "In what follows we refer to this quantity as the Ekeland–Hofer–Zehnder capacity and denote it by $c_{\rm EHZ}$." p. 10: "a closed characteristic of a smooth convex domain $\Sigma \subset \mathbb R^{2n}$ is a loop $\gamma \subset \partial\Sigma$ such that $\dot\gamma(t)$ is a positive multiple of $J\nabla H(\gamma(t))$, where $H : \mathbb R^{2n} \to \mathbb R$ has $\Sigma$ as a sub-level set, and $J : \mathbb R^{2n} \to \mathbb R^{2n}$ is the standard complex structure $J^2 = -Id$." Then: "The action of a closed characteristic $\gamma$ is defined by $\mathcal A(\gamma) = \int_\lambda \gamma$, where $\lambda$ is a primitive of $\omega$. If $\Sigma$ is not smooth, one can define a generalized closed characteristic, roughly speaking, by changing the condition above to require that $\dot\gamma(t)$ is a positive multiple of a vector in $J\partial H(\gamma(t))$, where $\partial H$ is the sub-gradient of $H$ (see, e.g., [45])." The definition follows [10] (Artstein-Avidan–Ostrover, IMRN 2014, https://doi.org/10.1093/imrn/rns216), §2.3, Definition 2.6: "A generalized closed characteristic on a (possibly singular) convex hypersurface $\Sigma \subset \mathbb R^{2n}$ is the image of a piecewise smooth loop $\gamma\colon S^1 \to \partial\Sigma$ which satisfies that for every $t \in S^1$ one has: $\dot\gamma^\pm(t) \in JN_\Sigma(\gamma(t))$."
--   - `phaseInner` is the Euclidean inner product of $\mathbb R^{2n}$ and `J (q, p) = (-p, q)` the complex structure of [10, §2.1]. `normalCone` is the outer normal cone $N_\Sigma(x) = \{u : \langle u, y - x\rangle \le 0 \text{ for all } y \in \Sigma\}$.
--   - `IsGeneralizedClosedCharacteristic S γ` is the paper's p. 10 condition with the loop parametrized by $\mathbb R$ with period $1$: an absolutely continuous loop on $\partial S$, $\gamma(b) - \gamma(a) = \int_a^b v$ with $v$ locally integrable, whose velocity lies in $J N_S(\gamma(t))$ for almost every $t$. For $\Sigma = \{H \le 1\}$ with $H$ convex, $\min H < 1$ and $x \in \partial\Sigma$, the positive multiples of $J\partial H(x)$ are the nonzero vectors of $J N_\Sigma(x)$; the velocity may also vanish, which only pauses the loop. [10, Def. 2.6] asks for piecewise smooth loops; the paper's own p. 10 description fixes no regularity, and the absolutely continuous class is taken here. That the infimum over this class is attained, and agrees on convex domains with a symplectic capacity, is the milestone `Viterbo.exists_isSymplecticCapacity_eq_cEHZ_and_exists_action_eq_cEHZ`.
--   - `action γ` is $\mathcal A(\gamma) = \frac12\int_0^1 \langle J\gamma(t), \dot\gamma(t)\rangle\,dt$ ([10, §2.2], with period $1$ in place of $2\pi$). With $J(q, p) = (-p, q)$ this is $-\int_\gamma \sum_i p_i\,dq_i$, the negative of the integral of $\lambda = \sum_i p_i\,dq_i$ along $\gamma$, which is what the paper's p. 10 formula, printed $\int_\lambda \gamma$, means; $c_{\rm EHZ}$ uses $|\mathcal A(\gamma)|$, so the sign changes nothing.
--   - `cEHZ S` is the infimum of $|\mathcal A(\gamma)|$ over the generalized closed characteristics that are not constant. A constant loop satisfies [10, Def. 2.6] (as $0 \in JN_S$) and has action $0$; the closed characteristics of the smooth case, embedded circles, are never constant.
--   - p. 5: "for a convex domain $A \subset \mathbb R^{2n}$, we denote the symplectic systolic ratio of $A$ by $\mathrm{Sys}(A) := \frac{c_{\rm EHZ}(A)^n}{n!\,\mathrm{Vol}(A)}$." This is `systolicRatio`, and `maxSystolicRatio n` is $\mathrm{Sys}(\mathcal K^{2n})$, the supremum over convex domains (p. 6).
--
--   **Minkowski billiards.** p. 8: "let $K \subset \mathbb R^n_q$ be a convex domain (the billiard table), and let $T \subset \mathbb R^n_p$ be a convex domain which has the origin in its interior. The corresponding Minkowski geometry induced by $T$ is given by the support function $h_T(u) := \sup\{\langle x, u\rangle \mid x \in T\}$". p. 8: "Recall that for a convex domain $K \subset \mathbb R^n$, the outer normal cone to $K$ at $x \in \partial K$ is defined as $N_K(x) = \{u \in \mathbb R^n \mid \langle u, y - x\rangle \le 0 \text{ for all } y \in K\}$." p. 4: "for a closed $T$-billiard trajectory in $K$ described by a polygonal curve $\gamma$ with vertices $q_1, q_2, \dots, q_m$, where $q_i \in \partial K$, the $T^\circ$-length of $\gamma$ is given by $\mathrm{Length}_{T^\circ}(\gamma) = \sum_{i=1}^m h_T(q_{i+1} - q_i)$, where $q_{m+1} = q_1$."
--   - `supportFunction`, `normalConeE` and `polygonLength` are these; a polygonal curve with $m$ vertices is a map `Fin m → Position n`, its indices read modulo $m$.
--   - p. 9: "Definition 2.1 (Minkowski Billiards). A closed polygonal curve with vertices $q_1, \dots, q_m$, $m \in \mathbb N_{\ge 2}$, on $\partial K$ is a closed $T$-billiard trajectory in $K$ if there are points $p_1, \dots, p_m$ on $\partial T$ such that for every $1 \le j \le m$, $q_{j+1} - q_j \in N_T(p_j)$, $p_{j+1} - p_j \in -N_K(q_{j+1})$." This is `IsClosedBilliard`. Definition 2.1 as printed does not ask for it, but consecutive vertices of the polygonal curve are taken distinct; otherwise a constant "curve" with constant $p_j$ would satisfy both conditions with length $0$.
--   - p. 9: "$\mathcal P(K) = \{(q_1, \dots, q_m) \mid \{q_1, \dots, q_m\} \not\subset \mathrm{int}(K) + t,\ \forall t \in \mathbb R^n\}$." This is `NotTranslatableIntoInterior`.
--
--   **Products and the pentagons.** p. 5: "Recall that for two subsets $X \subset \mathbb R^m$ and $Y \subset \mathbb R^n$ containing the origin, and for $1 \le p \le \infty$, their $p$-product is defined as $X \otimes_p Y := \bigcup_{0\le t\le 1}\big((1-t)^{1/p}X \times t^{1/p}Y\big) \subset \mathbb R^m \times \mathbb R^n$."
--   - `pProduct p X Y` is this subset of $\mathbb R^{m+k}$ (coordinates appended by `appendPos`), with $1/\infty = 0$.
--   - `symplecticPProduct p X Y` is the $p$-product of $X \subset \mathbb R^{2m}$ and $Y \subset \mathbb R^{2k}$ in $\mathbb R^{2(m+k)}$, the phase coordinates $((q, p), (q', p'))$ arranged as $((q, q'), (p, p'))$ so that the product of symplectic spaces is the standard one.
--   - p. 4: "Let $K \subset \mathbb R^2_q$ be the regular pentagon with vertices $\{(\cos(\frac{2\pi k}{5}), \sin(\frac{2\pi k}{5}))\}_{k=0}^4$, and let $T \subset \mathbb R^2_p$ be a rotation of $K$ by $90^o$, i.e., the vertices of $T$ are $\{(\cos(-\frac\pi2 + \frac{2\pi k}{5}), \sin(-\frac\pi2 + \frac{2\pi k}{5}))\}_{k=0}^4$." `pentagonK` and `pentagonT` are the closed convex hulls of these vertices. The explicit vertex list of $T$, and Figure 1, make $T$ the rotation of $K$ by $-90°$ (clockwise); the list is what is formalized.
-- source:
--   Haim-Kislev, P. and Ostrover, Y., A counterexample to Viterbo's conjecture, Ann. of Math. (2) 203 (2026) 603–622, https://doi.org/10.4007/annals.2026.203.2.5 (arXiv:2405.16513v3, whose page numbers are used), pp. 2–9, §1 (convex domains, Definition 1.1, Conjecture 1.2, c_G, c_Z, c_EHZ, Sys, p-products, the pentagons) and §2 (support function, normal cone, Definition 2.1, P(K)), with generalized closed characteristics from Artstein-Avidan, S. and Ostrover, Y., Bounds for Minkowski billiard trajectories in convex bodies, Int. Math. Res. Not. IMRN 2014, 165–193, https://doi.org/10.1093/imrn/rns216, §2.3

import Mathlib
import Definitions.Def_SymmetricPolar

/-!
# Symplectic capacities, Viterbo's conjecture, Minkowski billiards and the Ekeland–Hofer–Zehnder capacity

P. Haim-Kislev and Y. Ostrover, *A counterexample to Viterbo's conjecture*, Ann. of Math. 203 (2026)
603–622, arXiv:2405.16513v3 (HKO; page numbers are those of the arXiv version), and S. Artstein-Avidan and
Y. Ostrover, *Bounds for Minkowski billiard trajectories in convex bodies*, IMRN 2014, §2.3 (AAO), for
generalized closed characteristics.

Conventions:
- Phase space ℝ²ⁿ is `OAI.SymmetricPolar.Phase n = Position n × Position n`, points `z = (q, p)`, with
  `Position n = EuclideanSpace ℝ (Fin n)`; symplectic embeddings are `OAI.SymmetricPolar.HasSymplecticEmbedding`
  and the Gromov width is `OAI.SymmetricPolar.gromovWidth`.
- `phaseInner` is the Euclidean inner product of ℝ²ⁿ, `⟨(q, p), (q', p')⟩ = ⟨q, q'⟩ + ⟨p, p'⟩`; the
  complex structure is `J (q, p) = (-p, q)`.
- Volume on phase space is the product of the Lebesgue measures of the two factors.
- Capacities and volumes take values in `[0, ∞]`.
- A polygonal curve with `m` vertices is `q : Fin m → Position n`; its indices are read modulo `m`.
-/

namespace Viterbo

open OAI.SymmetricPolar MeasureTheory Set
open scoped ENNReal Pointwise

/-! ## Convex domains, balls, cylinders (HKO p. 2) -/

/-- HKO p. 2: "the term convex domain refers to a bounded convex set with nonempty interior". -/
def IsConvexDomain {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (S : Set E) : Prop :=
  Bornology.IsBounded S ∧ Convex ℝ S ∧ (interior S).Nonempty

/-- The cylinder `Z²ⁿ(r) = B²(r) × ℂⁿ⁻¹` of capacity `c = πr²`: the points whose first coordinate pair
`(q₁, p₁)` satisfies `π(q₁² + p₁²) < c`. -/
def capacityCylinder (n : ℕ) (c : ℝ) : Set (Phase n) :=
  {z | ∀ i : Fin n, i.val = 0 → Real.pi * (z.1 i ^ 2 + z.2 i ^ 2) < c}

/-- HKO p. 2: the cylindrical capacity `c_Z(U) = inf {πr² : U ↪ Z²ⁿ(r)}`. -/
noncomputable def cylindricalCapacity {n : ℕ} (U : Set (Phase n)) : ℝ≥0∞ :=
  sInf (ENNReal.ofReal '' {c : ℝ | 0 < c ∧ HasSymplecticEmbedding U (capacityCylinder n c)})

/-- HKO Definition 1.1: a symplectic capacity on `ℝ²ⁿ`, a `[0, ∞]`-valued function on all subsets that is
monotone under symplectic embeddings, conformal (`c(αU) = α² c(U)` for `α > 0`), and normalized:
`c(B²ⁿ(1)) = c(Z²ⁿ(1)) = π`. -/
def IsSymplecticCapacity (n : ℕ) (c : Set (Phase n) → ℝ≥0∞) : Prop :=
  (∀ U V : Set (Phase n), HasSymplecticEmbedding U V → c U ≤ c V) ∧
    (∀ (α : ℝ), 0 < α → ∀ U : Set (Phase n), c (α • U) = ENNReal.ofReal (α ^ 2) * c U) ∧
    c (capacityBall n Real.pi) = ENNReal.ofReal Real.pi ∧
    c (capacityCylinder n Real.pi) = ENNReal.ofReal Real.pi

/-- HKO Conjecture 1.2 (Viterbo, 2000) in `ℝ²ⁿ`: `c(K)ⁿ ≤ n! Vol(K)` for every symplectic capacity `c` and
every convex domain `K`. -/
def ViterboConjecture (n : ℕ) : Prop :=
  ∀ c : Set (Phase n) → ℝ≥0∞, IsSymplecticCapacity n c →
    ∀ K : Set (Phase n), IsConvexDomain K → c K ^ n ≤ (n.factorial : ℝ≥0∞) * volume K

/-- A symplectomorphism of `U` onto `V`: a symplectic embedding of `U` whose image is `V`. -/
def IsSymplectomorphic {n : ℕ} (U V : Set (Phase n)) : Prop :=
  ∃ e : Phase n → Phase n,
    ContDiffOn ℝ (⊤ : ℕ∞) e U ∧
    Topology.IsEmbedding (fun z : U => e z) ∧
    e '' U = V ∧
    ∀ z ∈ U, ∀ v w : Phase n, omega0 (fderiv ℝ e z v) (fderiv ℝ e z w) = omega0 v w

/-! ## Support functions, normal cones, Minkowski billiards (HKO pp. 3–9) -/

section Billiards

variable {n : ℕ}

/-- HKO p. 3: the support function `h_T(u) = sup {⟨x, u⟩ : x ∈ T}`. -/
noncomputable def supportFunction (T : Set (Position n)) (u : Position n) : ℝ :=
  sSup ((fun x => inner (𝕜 := ℝ) x u) '' T)

/-- HKO p. 8: the outer normal cone `N_K(x) = {u : ⟨u, y - x⟩ ≤ 0 for all y ∈ K}`. -/
def normalCone {E : Type*} (inner' : E → E → ℝ) [Sub E] (K : Set E) (x : E) : Set E :=
  {u | ∀ y ∈ K, inner' u (y - x) ≤ 0}

/-- The outer normal cone in `ℝⁿ`. -/
def normalConeE (K : Set (Position n)) (x : Position n) : Set (Position n) :=
  normalCone (fun u v => inner (𝕜 := ℝ) u v) K x

/-- HKO p. 4: the `T°`-length `∑ᵢ h_T(q_{i+1} - q_i)` of the closed polygonal curve with vertices
`q₁, …, q_m` (indices modulo `m`). -/
noncomputable def polygonLength {m : ℕ} (T : Set (Position n)) (q : Fin m → Position n) : ℝ :=
  ∑ i : Fin m, supportFunction T (q (finRotate m i) - q i)

/-- HKO Definition 2.1: the closed polygonal curve with vertices `q₁, …, q_m`, `m ≥ 2`, on `∂K` is a closed
`T`-billiard trajectory in `K`: there are `p₁, …, p_m` on `∂T` with `q_{j+1} - q_j ∈ N_T(p_j)` and
`p_{j+1} - p_j ∈ -N_K(q_{j+1})` (indices modulo `m`). Consecutive vertices of a polygonal curve are
distinct. -/
def IsClosedBilliard {m : ℕ} (K T : Set (Position n)) (q : Fin m → Position n) : Prop :=
  2 ≤ m ∧ (∀ j, q j ∈ frontier K) ∧ (∀ j, q (finRotate m j) ≠ q j) ∧
    ∃ p : Fin m → Position n, ∀ j, p j ∈ frontier T ∧
      q (finRotate m j) - q j ∈ normalConeE T (p j) ∧
      p (finRotate m j) - p j ∈ -normalConeE K (q (finRotate m j))

/-- HKO p. 9: `P(K)`, the polygonal curves `(q₁, …, q_m)` that cannot be translated into the interior of
`K`: `{q₁, …, q_m} ⊄ int(K) + t` for every `t`. -/
def NotTranslatableIntoInterior {m : ℕ} (K : Set (Position n)) (q : Fin m → Position n) : Prop :=
  ∀ t : Position n, ¬ ∀ j, q j ∈ interior K + {t}

end Billiards

/-! ## Generalized closed characteristics and the Ekeland–Hofer–Zehnder capacity (HKO p. 2, AAO §2.3) -/

section EHZ

variable {n : ℕ}

/-- The Euclidean inner product of `ℝ²ⁿ`: `⟨(q, p), (q', p')⟩ = ⟨q, q'⟩ + ⟨p, p'⟩`. -/
noncomputable def phaseInner (z w : Phase n) : ℝ :=
  inner (𝕜 := ℝ) z.1 w.1 + inner (𝕜 := ℝ) z.2 w.2

/-- The standard complex structure `J (q, p) = (-p, q)` (AAO §2.1). -/
def J (z : Phase n) : Phase n := (-z.2, z.1)

/-- HKO p. 10: a generalized closed characteristic on the boundary of the convex set `Σ`, parametrized
with period `1`: an absolutely continuous loop on `∂Σ`, `γ(b) - γ(a) = ∫ₐᵇ v`, whose velocity `v`
lies in `J N_Σ(γ(t))` for almost every `t`. -/
def IsGeneralizedClosedCharacteristic (S : Set (Phase n)) (γ : ℝ → Phase n) : Prop :=
  Function.Periodic γ 1 ∧ (∀ t, γ t ∈ frontier S) ∧
    ∃ v : ℝ → Phase n, LocallyIntegrable v volume ∧
      (∀ a b, γ b - γ a = ∫ s in a..b, v s) ∧
      ∀ᵐ t, v t ∈ J '' normalCone phaseInner S (γ t)

/-- AAO §2.2: the action `A(γ) = ½ ∫ ⟨J γ(t), γ̇(t)⟩ dt` of a loop of period `1`. -/
noncomputable def action (γ : ℝ → Phase n) : ℝ :=
  (1 / 2) * ∫ t in (0 : ℝ)..1, phaseInner (J (γ t)) (deriv γ t)

/-- HKO p. 2 and footnote 1: the Ekeland–Hofer–Zehnder capacity of a convex domain, the minimal action
among (generalized) closed characteristics on its boundary; here the infimum of `|A(γ)|` over the
nonconstant generalized closed characteristics. -/
noncomputable def cEHZ (S : Set (Phase n)) : ℝ≥0∞ :=
  ⨅ (γ : ℝ → Phase n) (_ : IsGeneralizedClosedCharacteristic S γ ∧ ∃ s t, γ s ≠ γ t),
    ENNReal.ofReal |action γ|

/-- HKO p. 5: the symplectic systolic ratio `Sys(A) = c_EHZ(A)ⁿ / (n! Vol(A))`. -/
noncomputable def systolicRatio (A : Set (Phase n)) : ℝ≥0∞ :=
  cEHZ A ^ n / ((n.factorial : ℝ≥0∞) * volume A)

/-- HKO p. 6: `Sys(K²ⁿ)`, the supremum of the systolic ratio over the convex domains of `ℝ²ⁿ`. -/
noncomputable def maxSystolicRatio (n : ℕ) : ℝ≥0∞ :=
  ⨆ (A : Set (Phase n)) (_ : IsConvexDomain A), systolicRatio A

end EHZ

/-! ## p-products (HKO p. 5) -/

section Products

/-- The coordinates of `ℝᵐ × ℝᵏ` as one point of `ℝ^{m+k}`. -/
noncomputable def appendPos {m k : ℕ} (x : Position m) (y : Position k) : Position (m + k) :=
  (WithLp.equiv 2 (Fin (m + k) → ℝ)).symm (Fin.append (WithLp.equiv 2 _ x) (WithLp.equiv 2 _ y))

/-- HKO p. 5: the `p`-product `X ⊗_p Y = ⋃_{0 ≤ t ≤ 1} (1 - t)^{1/p} X × t^{1/p} Y ⊂ ℝᵐ × ℝᵏ`, for
`1 ≤ p ≤ ∞` (`1/∞ = 0`, giving the product `X × Y`), as a subset of `ℝ^{m+k}`. -/
noncomputable def pProduct {m k : ℕ} (p : ℝ≥0∞) (X : Set (Position m)) (Y : Set (Position k)) :
    Set (Position (m + k)) :=
  ⋃ t ∈ Icc (0 : ℝ) 1, (fun xy : Position m × Position k => appendPos xy.1 xy.2) ''
    ((((1 - t) ^ p⁻¹.toReal) • X) ×ˢ ((t ^ p⁻¹.toReal) • Y))

/-- The symplectic `p`-product of `X ⊂ ℝ²ᵐ` and `Y ⊂ ℝ²ᵏ` in `ℝ^{2(m+k)}`: the `p`-product, with the phase
coordinates `((q, p), (q', p'))` arranged as `((q, q'), (p, p'))`. -/
noncomputable def symplecticPProduct {m k : ℕ} (p : ℝ≥0∞) (X : Set (Phase m)) (Y : Set (Phase k)) :
    Set (Phase (m + k)) :=
  ⋃ t ∈ Icc (0 : ℝ) 1, (fun zw : Phase m × Phase k => (appendPos zw.1.1 zw.2.1, appendPos zw.1.2 zw.2.2)) ''
    ((((1 - t) ^ p⁻¹.toReal) • X) ×ˢ ((t ^ p⁻¹.toReal) • Y))

end Products

/-! ## The two pentagons (HKO p. 4) -/

/-- HKO p. 4: the vertex `(cos(2πk/5), sin(2πk/5))` of `K`. -/
noncomputable def pentagonVertex (k : ℕ) : Position 2 :=
  !₂[Real.cos (2 * Real.pi * k / 5), Real.sin (2 * Real.pi * k / 5)]

/-- HKO p. 4: the vertex `(cos(-π/2 + 2πk/5), sin(-π/2 + 2πk/5))` of `T`. -/
noncomputable def rotatedVertex (k : ℕ) : Position 2 :=
  !₂[Real.cos (-(Real.pi / 2) + 2 * Real.pi * k / 5), Real.sin (-(Real.pi / 2) + 2 * Real.pi * k / 5)]

/-- HKO p. 4: the regular pentagon `K ⊂ ℝ²_q` with vertices `(cos(2πk/5), sin(2πk/5))`, `k = 0, …, 4`. -/
noncomputable def pentagonK : Set (Position 2) :=
  convexHull ℝ (pentagonVertex '' Finset.range 5)

/-- HKO p. 4: the pentagon `T ⊂ ℝ²_p`, the rotation of `K` by `90°`. -/
noncomputable def pentagonT : Set (Position 2) :=
  convexHull ℝ (rotatedVertex '' Finset.range 5)

end Viterbo


