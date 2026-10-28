-- Prove2me | Definitions.Def_WildeQIT_FinDist
-- name    : WildeQIT_FinDist
-- status  : Definition
-- author  : @nonlocally
-- created : 2026-09-07T03:50:01.057724+00:00
-- url     : https://prove2.me/theorems/e913fd43-0684-4f39-a153-817af2408fd5
-- title:
--   Probability distribution on a finite alphabet (and marginals, reindexing, independence)
-- statement:
--   This file provides the basic classical object of Wilde's Chapter 10: a **probability distribution** $p_X$ of a discrete random variable $X$ taking values in a finite alphabet $\mathcal{X}$. Throughout Chapter 10 Wilde works with finite alphabets (cf. Definition 10.5.1, "Let $\mathcal{X}$ denote a finite set"), and every quantity of the chapter (entropy, conditional entropy, mutual information, relative entropy) depends on a random variable only through its distribution. Accordingly a random variable is represented by its distribution, a pair $(X,Y)$ by its joint distribution $p_{XY}$ on $\mathcal{X}\times\mathcal{Y}$, and a triple $(X,Y,Z)$ by $p_{XYZ}$ on $\mathcal{X}\times\mathcal{Y}\times\mathcal{Z}$.
--
--   **Distribution.** `WildeQIT.FinDist α` bundles a function $p:\alpha\to\mathbb{R}$ with the two axioms of a probability distribution on the finite alphabet $\alpha$:
--
--   $$
--   p(x)\ge 0 \ \text{ for all } x\in\alpha, \qquad \sum_{x\in\alpha} p(x) = 1 .
--   $$
--
--   (Consequently $\alpha$ is non-empty and every $p(x)\le 1$; the latter is the lemma `prob_le_one`.)
--
--   **Marginals and reindexing.** For a joint distribution $p$ on $\alpha\times\beta$: `fst` is the marginal $p_X(x)=\sum_y p(x,y)$, `snd` is $p_Y(y)=\sum_x p(x,y)$, and `swap` is $p_{YX}(y,x)=p(x,y)$. `comap e` reindexes a distribution along a bijection $e:\beta\simeq\alpha$, $(p\circ e)(b)=p(e(b))$, which is how permutations of the alphabet act. `map f` is the push-forward along an arbitrary function $f:\alpha\to\beta$ (the distribution of $f(X)$): $(f_*p)(b)=\sum_{a: f(a)=b}p(a)$. `prod p q` is the product distribution $p(x)q(y)$ of two independent variables.
--
--   **Independence.** `Indep p` says that $X$ and $Y$ with joint distribution $p$ are independent, in Wilde's sense (Theorem 10.4.1): $p_{XY}(x,y)=p_X(x)\,p_Y(y)$ for all $x,y$.
--
--   **Three variables.** For $p=p_{XYZ}$ on $\alpha\times\beta\times\gamma$ the file provides the three pair-marginals $p_{XY}(x,y)=\sum_z p(x,y,z)$ (`margXY`), $p_{XZ}$ (`margXZ`), $p_{YZ}$ (`margYZ`), and two regroupings that present the same joint distribution as a *pair* distribution: `groupXY_Z` views it as the pair $((X,Y),Z)$ and `groupY_XZ` as the pair $(Y,(X,Z))$; these feed the two-variable conditional entropy to express $H(XY|Z)$ and $H(Y|XZ)$.
--
--   **Many variables.** For a joint distribution on $\prod_{i<n}\alpha_i$ (Lean: `∀ i : Fin n, α i`), `margin i` is the marginal of the $i$-th coordinate, $p_{X_i}(a)=\sum_{x:\,x_i=a}p(x)$.
--
--   **Formalization Note.** All probabilities are real numbers; sums are finite sums over the alphabet. The type of alphabets is `Type` (not universe-polymorphic) by book-wide convention. Every projection lemma (`fst_prob`, `snd_prob`, `comap_prob`, `swap_prob`, `map_prob`, `prod_prob`, `margXY_prob`, `margXZ_prob`, `margYZ_prob`, `groupXY_Z_prob`, `groupY_XZ_prob`, `margin_prob`) holds by `rfl` and is tagged `simp` where the left-hand side is in simp-normal form.
-- source:
--   Wilde, Quantum Information Theory, 2nd ed. (Cambridge University Press, 2017; arXiv:1106.1445v8), Chapter 10 (Classical Information and Entropy), §10.1 (setting: discrete random variable with distribution p_X on a finite alphabet 𝒳; cf. Definition 10.5.1 'Let 𝒳 denote a finite set'), pairs and triples of random variables as in §10.2–10.6; independence as in Theorem 10.4.1.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Logic.Equiv.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
Wilde, *Quantum Information Theory* (2nd ed.), Chapter 10 (Classical Information and Entropy).
Core classical object: a probability distribution `p_X` of a discrete random variable `X`
taking values in a finite alphabet `𝒳` (Wilde works with finite alphabets throughout Ch. 10,
cf. Definition 10.5.1 "Let 𝒳 denote a finite set"). A random variable is represented by its
distribution; a pair `(X,Y)` by its joint distribution `p_{XY}` on `𝒳 × 𝒴`; a triple `(X,Y,Z)`
by `p_{XYZ}` on `𝒳 × 𝒴 × 𝒵` (which is `𝒳 × (𝒴 × 𝒵)`).
-/

namespace WildeQIT

/-- A probability distribution on a finite alphabet `α`: a real-valued function `prob` on `α`
that is non-negative and sums to one. -/
structure FinDist (α : Type) [Fintype α] where
  /-- The probability mass `p(x)` of the letter `x`. -/
  prob : α → ℝ
  /-- Probabilities are non-negative. -/
  nonneg : ∀ x, 0 ≤ prob x
  /-- Probabilities sum to one. -/
  sum_eq_one : ∑ x, prob x = 1

namespace FinDist

variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]

/-- Every probability is at most one. -/
theorem prob_le_one (p : FinDist α) (x : α) : p.prob x ≤ 1 := by
  rw [← p.sum_eq_one]
  exact Finset.single_le_sum (fun y _ => p.nonneg y) (Finset.mem_univ x)

/-- Marginal distribution of the first component: `p_X(x) = ∑_y p_{XY}(x,y)`. -/
noncomputable def fst (p : FinDist (α × β)) : FinDist α where
  prob x := ∑ y, p.prob (x, y)
  nonneg x := Finset.sum_nonneg fun y _ => p.nonneg (x, y)
  sum_eq_one := by rw [← Fintype.sum_prod_type]; exact p.sum_eq_one

/-- Marginal distribution of the second component: `p_Y(y) = ∑_x p_{XY}(x,y)`. -/
noncomputable def snd (p : FinDist (α × β)) : FinDist β where
  prob y := ∑ x, p.prob (x, y)
  nonneg y := Finset.sum_nonneg fun x _ => p.nonneg (x, y)
  sum_eq_one := by rw [Finset.sum_comm, ← Fintype.sum_prod_type]; exact p.sum_eq_one

@[simp] theorem fst_prob (p : FinDist (α × β)) (x : α) : p.fst.prob x = ∑ y, p.prob (x, y) := rfl
@[simp] theorem snd_prob (p : FinDist (α × β)) (y : β) : p.snd.prob y = ∑ x, p.prob (x, y) := rfl

/-- Reindexing a distribution along a bijection `e : β ≃ α`: `(p.comap e)(b) = p(e b)`. -/
def comap (e : β ≃ α) (p : FinDist α) : FinDist β where
  prob b := p.prob (e b)
  nonneg b := p.nonneg (e b)
  sum_eq_one := by rw [Equiv.sum_comp e p.prob]; exact p.sum_eq_one

@[simp] theorem comap_prob (e : β ≃ α) (p : FinDist α) (b : β) : (p.comap e).prob b = p.prob (e b) := rfl

/-- The joint distribution with the two components exchanged: `p_{YX}(y,x) = p_{XY}(x,y)`. -/
def swap (p : FinDist (α × β)) : FinDist (β × α) := p.comap (Equiv.prodComm β α)

@[simp] theorem swap_prob (p : FinDist (α × β)) (y : β) (x : α) : p.swap.prob (y, x) = p.prob (x, y) := rfl

/-- `X` and `Y` are independent random variables: `p_{XY}(x,y) = p_X(x) p_Y(y)` for all `x, y`. -/
def Indep (p : FinDist (α × β)) : Prop := ∀ x y, p.prob (x, y) = p.fst.prob x * p.snd.prob y

/-- Pushforward of a distribution along a map `f : α → β`: `(p.map f)(b) = ∑_{a : f a = b} p(a)`,
the distribution of the random variable `f(X)`. -/
noncomputable def map [DecidableEq β] (f : α → β) (p : FinDist α) : FinDist β where
  prob b := ∑ a ∈ Finset.univ.filter (fun a => f a = b), p.prob a
  nonneg b := Finset.sum_nonneg fun a _ => p.nonneg a
  sum_eq_one := by
    rw [Finset.sum_fiberwise Finset.univ f p.prob]
    exact p.sum_eq_one

@[simp] theorem map_prob [DecidableEq β] (f : α → β) (p : FinDist α) (b : β) :
    (p.map f).prob b = ∑ a ∈ Finset.univ.filter (fun a => f a = b), p.prob a := rfl

/-- Product distribution `(p ⊗ q)(x, y) = p(x) q(y)` of two independent random variables. -/
noncomputable def prod (p : FinDist α) (q : FinDist β) : FinDist (α × β) where
  prob xy := p.prob xy.1 * q.prob xy.2
  nonneg xy := mul_nonneg (p.nonneg xy.1) (q.nonneg xy.2)
  sum_eq_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul, q.sum_eq_one, p.sum_eq_one, mul_one]

@[simp] theorem prod_prob (p : FinDist α) (q : FinDist β) (x : α) (y : β) :
    (p.prod q).prob (x, y) = p.prob x * q.prob y := rfl

/-! ### Finitely many random variables `X₁, …, Xₙ` with joint distribution on `∀ i, α i` -/

/-- Marginal distribution of the `i`-th coordinate of a joint distribution on `∀ i, α i`:
`p_{X_i}(a) = ∑_{x : x_i = a} p(x)`. -/
noncomputable def margin {n : ℕ} {α : Fin n → Type} [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    (p : FinDist (∀ i, α i)) (i : Fin n) : FinDist (α i) :=
  p.map (fun x => x i)

theorem margin_prob {n : ℕ} {α : Fin n → Type} [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    (p : FinDist (∀ i, α i)) (i : Fin n) (a : α i) :
    (p.margin i).prob a = ∑ x ∈ Finset.univ.filter (fun x => x i = a), p.prob x := rfl

/-! ### Three random variables `(X, Y, Z)` with joint distribution on `α × β × γ` -/

/-- Marginal `p_{XY}(x,y) = ∑_z p_{XYZ}(x,y,z)`. -/
noncomputable def margXY (p : FinDist (α × β × γ)) : FinDist (α × β) where
  prob xy := ∑ z, p.prob (xy.1, xy.2, z)
  nonneg xy := Finset.sum_nonneg fun z _ => p.nonneg (xy.1, xy.2, z)
  sum_eq_one := by
    have h := p.sum_eq_one
    rw [Fintype.sum_prod_type] at h
    simp_rw [Fintype.sum_prod_type] at h
    rw [Fintype.sum_prod_type]
    exact h

/-- Marginal `p_{XZ}(x,z) = ∑_y p_{XYZ}(x,y,z)`. -/
noncomputable def margXZ (p : FinDist (α × β × γ)) : FinDist (α × γ) where
  prob xz := ∑ y, p.prob (xz.1, y, xz.2)
  nonneg xz := Finset.sum_nonneg fun y _ => p.nonneg (xz.1, y, xz.2)
  sum_eq_one := by
    have h := p.sum_eq_one
    rw [Fintype.sum_prod_type] at h
    simp_rw [Fintype.sum_prod_type] at h
    rw [Fintype.sum_prod_type]
    simp_rw [Finset.sum_comm (γ := γ)]
    exact h

/-- Marginal `p_{YZ}(y,z) = ∑_x p_{XYZ}(x,y,z)`. -/
noncomputable def margYZ (p : FinDist (α × β × γ)) : FinDist (β × γ) where
  prob yz := ∑ x, p.prob (x, yz)
  nonneg yz := Finset.sum_nonneg fun x _ => p.nonneg (x, yz)
  sum_eq_one := by
    have h := p.sum_eq_one
    rw [Fintype.sum_prod_type] at h
    rw [Finset.sum_comm]
    exact h

@[simp] theorem margXY_prob (p : FinDist (α × β × γ)) (x : α) (y : β) :
    p.margXY.prob (x, y) = ∑ z, p.prob (x, y, z) := rfl
@[simp] theorem margXZ_prob (p : FinDist (α × β × γ)) (x : α) (z : γ) :
    p.margXZ.prob (x, z) = ∑ y, p.prob (x, y, z) := rfl
@[simp] theorem margYZ_prob (p : FinDist (α × β × γ)) (y : β) (z : γ) :
    p.margYZ.prob (y, z) = ∑ x, p.prob (x, y, z) := rfl

/-- Regrouping `(x, y, z) ↦ ((x, y), z)`, the pair `(XY, Z)`. -/
def groupXY_Z (p : FinDist (α × β × γ)) : FinDist ((α × β) × γ) :=
  p.comap (Equiv.prodAssoc α β γ)

/-- Regrouping `(x, y, z) ↦ (y, (x, z))`, the pair `(Y, XZ)`. -/
def groupY_XZ (p : FinDist (α × β × γ)) : FinDist (β × (α × γ)) :=
  p.comap ⟨fun t => (t.2.1, t.1, t.2.2), fun t => (t.2.1, t.1, t.2.2), fun _ => rfl, fun _ => rfl⟩

@[simp] theorem groupXY_Z_prob (p : FinDist (α × β × γ)) (x : α) (y : β) (z : γ) :
    p.groupXY_Z.prob ((x, y), z) = p.prob (x, y, z) := rfl
@[simp] theorem groupY_XZ_prob (p : FinDist (α × β × γ)) (x : α) (y : β) (z : γ) :
    p.groupY_XZ.prob (y, (x, z)) = p.prob (x, y, z) := rfl

end FinDist

end WildeQIT


