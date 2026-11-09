-- Prove2me | Definitions.Def_ElimAgree_IsLaw
-- name    : ElimAgree_IsLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:15:26.675653+00:00
-- url     : https://prove2.me/theorems/5344b5c5-29dc-486c-aefa-66ec2824d0d4
-- title:
--   Laws, channels, product laws, tensor channels and conditioning on finite sets
-- statement:
--   A **law** on a finite set $X$ is a vector $(p_x)$ with $p_x\ge0$ and $\sum_x p_x=1$. A **channel** $\kappa$ from $X$ to $Y$ is a matrix each of whose rows $\kappa(x,\cdot)$ is a law on $Y$; the law of the output on an input drawn from $P$ is
--   $$(P\kappa)(y)=\sum_x P(x)\,\kappa(x,y).$$
--   For laws $\pi_i$ on $X_i$ the **product law** is $(\otimes_i\pi_i)(x)=\prod_i\pi_i(x_i)$, and for channels $\kappa_i$ the **tensor channel** $\otimes_i\kappa_i$ draws each $J_i$ from $\kappa_i(x_i,\cdot)$ independently: $(\otimes_i\kappa_i)(x,y)=\prod_i\kappa_i(x_i,y_i)$. The **conditional law** $\pi(\cdot\mid A)$ is $\pi(x)/\pi(A)$ on $A$ and $0$ off $A$. The uniform law gives every point mass $1/|X|$.
--
--   These are the objects of §3.2.
--
--   **Formalization Note** Laws are real-valued functions on finite types, the encoding of the reused definitions of relative entropy and Hellinger distance.
-- source:
--   Ben Daniel, Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination, manuscript (STOC 2027 submission; held version sha256 eea57875…), §3.2, p.8 (PDF p.10)

import Mathlib

namespace ElimAgree

/-- A law (probability distribution) on a finite type: nonnegative weights summing to `1` (Ben
Daniel, *Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination*,
manuscript, STOC 2027 submission, §3, pp.7–8). -/
def IsLaw {ι : Type} [Fintype ι] (p : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

/-- A channel from `X` to `Y` (§3.2, p.8): every row `κ x` is a law on `Y`. -/
def IsChannel {X Y : Type} [Fintype Y] (κ : X → Y → ℝ) : Prop :=
  ∀ x, IsLaw (κ x)

/-- The law `Pκ` of the output of the channel `κ` on an input drawn from `P` (p.8):
`(Pκ)(y) = Σ_x P(x) κ(x, y)`. -/
noncomputable def pushLaw {X Y : Type} [Fintype X] (P : X → ℝ) (κ : X → Y → ℝ) : Y → ℝ :=
  fun y => ∑ x, P x * κ x y

/-- The uniform law on a finite type. -/
noncomputable def uniformLaw (ι : Type) [Fintype ι] : ι → ℝ :=
  fun _ => 1 / (Fintype.card ι : ℝ)

/-- The product law `⊗_i π_i` on `Π_i X_i` (p.8): `(⊗π)(x) = Π_i π_i(x_i)`. -/
def prodLaw {r : ℕ} {X : Fin r → Type} (π : ∀ i, X i → ℝ) : (∀ i, X i) → ℝ :=
  fun x => ∏ i, π i (x i)

/-- The tensor channel `⊗_i κ_i` from `Π_i X_i` to `Π_i Y_i` (p.8): each `J_i` is drawn from
`κ_i(X_i, ·)` independently given `X`, so `(⊗κ)(x, y) = Π_i κ_i(x_i, y_i)`. -/
def tensorChannel {r : ℕ} {X Y : Fin r → Type} (κ : ∀ i, X i → Y i → ℝ) :
    (∀ i, X i) → (∀ i, Y i) → ℝ :=
  fun x y => ∏ i, κ i (x i) (y i)

/-- The conditional law `π(· | A)` (Corollary 3.4, p.8): `π(x)/π(A)` on `A` and `0` off `A`.
It is a law whenever `π(A) > 0`. -/
noncomputable def condLaw {X : Type} [DecidableEq X] (π : X → ℝ) (A : Finset X) : X → ℝ :=
  fun x => if x ∈ A then π x / (∑ y ∈ A, π y) else 0

end ElimAgree


