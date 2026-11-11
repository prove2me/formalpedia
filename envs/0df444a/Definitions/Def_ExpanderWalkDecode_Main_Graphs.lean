-- Prove2me | Definitions.Def_ExpanderWalkDecode_Main_Graphs
-- name    : ExpanderWalkDecode_Main_Graphs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:20:38.766196+00:00
-- url     : https://prove2.me/theorems/0e966da4-a482-497e-95fa-cb4b90087e10
-- title:
--   Rotation-map regular graphs, $\lambda$-expanders, local invertibility, Cayley graphs over $\mathbb F_2$, averages and the operator norm
-- statement:
--   A **$d$-regular undirected graph** on a vertex set $V$ with port set $P$ ($|P|=d$) is a rotation map $\mathrm{Rot}: V\times P\to V\times P$ that is an involution: $\mathrm{Rot}(v,i)=(w,j)$ says that the $i$-th edge at $v$ leads to $w$ and arrives there as the $j$-th edge of $w$; self-loops and parallel edges are allowed. The $i$-th neighbour of $v$ is written $\varphi(v,i)$. The normalized adjacency operator is $(M f)(v) = d^{-1}\sum_{i\in P} f(\varphi(v,i))$, and the graph is a **$\lambda$-expander** if
--   $$|\langle x, M y\rangle| \le \lambda\,\|x\|\,\|y\| \qquad\text{for all } x,y\in\mathbb R^V \text{ with } \textstyle\sum_v x_v = \sum_v y_v = 0.$$
--   It is **locally invertible** if for every port $i$ there is a port $i'$ with $\varphi(\varphi(v,i),i')=v$ for every vertex $v$.
--
--   For an $\mathbb F_2$-vector space $M$ and a generator family $u_1,\dots,u_q\in M$ (a multiset), the **Cayley graph** has rotation map $(b,j)\mapsto(b+u_j, j)$; it is $q$-regular and undirected.
--
--   The file also fixes the uniform average $\mathbb E_{i}$ over a finite set, the Euclidean operator norm $\|\cdot\|_{\mathrm{op}}$ of a real square matrix, and the probability that $\ell$ independent uniform samples from a finite set satisfy an event (the fraction of $\ell$-tuples satisfying it).
-- source:
--   Silas Richelson, Sourya Roy, Madhur Tulsiani, Decoding Expander Walk Codes up to the Johnson Bound in Near-Linear Time, STOC 2027 submission #1736 (October 2026), p. 10 (§3.3, λ-expander), pp. 21–22 (Appendix B, Cayley graphs; B.1, rotation maps and local invertibility)

import Mathlib

namespace ExpanderWalkDecode.Main

open scoped Matrix.Norms.L2Operator

/-!
# Regular graphs by rotation maps, expansion, local invertibility, Cayley graphs over `F₂`,
# uniform averages and the matrix operator norm

Source: §3.3 (p. 10) for `λ`-expanders; Appendix B and B.1 (pp. 21–22) for rotation maps, local
invertibility and Cayley graphs.

A `d`-regular undirected graph on `V` with port set `P` (`|P| = d`) is a rotation map
`Rot : V × P → V × P` that is an involution: `Rot (v, i) = (w, j)` says the `i`-th edge at `v`
leads to `w` and arrives there as its `j`-th edge. Self-loops and parallel edges are allowed. The
normalized adjacency operator averages over the `d` neighbours. The graph is a `λ`-expander when
`|⟨x, M y⟩| ≤ λ ‖x‖ ‖y‖` for all `x, y ⊥ 𝟙`.
-/

/-- A regular undirected graph on `V` with port set `P`, given by an involutive rotation map. -/
structure RotGraph (V P : Type) where
  rot : V × P → V × P
  invol : Function.Involutive rot

namespace RotGraph

variable {V P : Type}

/-- The `i`-th neighbour of `v`. -/
def nbr (G : RotGraph V P) (v : V) (i : P) : V := (G.rot (v, i)).1

/-- The normalized adjacency operator `(M f)(v) = |P|⁻¹ ∑_i f(nbr v i)`. -/
noncomputable def adj [Fintype P] (G : RotGraph V P) (f : V → ℝ) : V → ℝ :=
  fun v => (Fintype.card P : ℝ)⁻¹ * ∑ i, f (G.nbr v i)

/-- `G` is a `λ`-expander (§3.3): `|⟨x, M y⟩| ≤ λ ‖x‖ ‖y‖` for all `x, y` orthogonal to the
all-ones vector. -/
def IsExpander [Fintype V] [Fintype P] (G : RotGraph V P) (lam : ℝ) : Prop :=
  ∀ x y : V → ℝ, ∑ v, x v = 0 → ∑ v, y v = 0 →
    |∑ v, x v * G.adj y v| ≤ lam * Real.sqrt (∑ v, x v ^ 2) * Real.sqrt (∑ v, y v ^ 2)

/-- Local invertibility (Appendix B.1, p. 22): for every port `i` there is a port `i'` with
`nbr (nbr v i) i' = v` for every vertex `v`. -/
def LocallyInvertible (G : RotGraph V P) : Prop :=
  ∀ i : P, ∃ i' : P, ∀ v : V, G.nbr (G.nbr v i) i' = v

end RotGraph

/-- In an `F₂`-vector space every element is its own negative. -/
theorem add_self_eq_zero_of_zmod2 {M : Type} [AddCommGroup M] [Module (ZMod 2) M] (x : M) :
    x + x = 0 := by
  have h : x + x = ((1 : ZMod 2) + 1) • x := by rw [add_smul, one_smul]
  rw [h]
  have h2 : ((1 : ZMod 2) + 1) = 0 := by decide
  rw [h2, zero_smul]

/-- The Cayley graph of the elementary abelian `2`-group `M` with generator family
`u : Fin q → M` (a multiset of `q` generators): the `j`-th edge at `b` leads to `b + u j`, and
arrives there as its `j`-th edge. It is `q`-regular and undirected because `u j = -u j`. -/
def cayley {M : Type} [AddCommGroup M] [Module (ZMod 2) M] {q : ℕ} (u : Fin q → M) :
    RotGraph M (Fin q) where
  rot := fun bj => (bj.1 + u bj.2, bj.2)
  invol := by
    rintro ⟨b, j⟩
    show (b + u j + u j, j) = (b, j)
    rw [add_assoc, add_self_eq_zero_of_zmod2, add_zero]

/-- The uniform average `|ι|⁻¹ ∑_i f i` (`0` on an empty type). -/
noncomputable def avg {ι M : Type} [Fintype ι] [AddCommGroup M] [Module ℝ M] (f : ι → M) : M :=
  (Fintype.card ι : ℝ)⁻¹ • ∑ i, f i

/-- The uniform average over a finite set `S` (`0` on the empty set). -/
noncomputable def favg {ι M : Type} [AddCommGroup M] [Module ℝ M] (S : Finset ι) (f : ι → M) : M :=
  (S.card : ℝ)⁻¹ • ∑ i ∈ S, f i

/-- The Euclidean (spectral) operator norm of a real square matrix. -/
noncomputable def opNorm {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ) : ℝ := ‖M‖

/-- The probability that `i.i.d.` uniform samples `v₁, …, v_ℓ ∈ V` satisfy `E`. -/
noncomputable def sampleProb {V : Type} [Fintype V] (ℓ : ℕ) (E : (Fin ℓ → V) → Prop) : ℝ :=
  (Nat.card {v : Fin ℓ → V // E v} : ℝ) / (Fintype.card V : ℝ) ^ ℓ

end ExpanderWalkDecode.Main


