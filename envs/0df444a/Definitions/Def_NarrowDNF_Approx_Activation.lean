-- Prove2me | Definitions.Def_NarrowDNF_Approx_Activation
-- name    : NarrowDNF_Approx_Activation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:06:34.342179+00:00
-- url     : https://prove2.me/theorems/52a5d3d8-54d9-45d3-82a9-033d4f783303
-- title:
--   Local activations, adaptive atoms, arity, load and forcing
-- statement:
--   For every coordinate subset $S$, an activation $J_S$ is an arbitrary Boolean function on the labels in $S$. Increasing activations means that every $J_S$ is coordinatewise increasing; this is a separate predicate. Define
--   $$A_J(x)=\bigcup_{S:J_S(x_S)=1}S,\qquad\Phi_J(x)=(A_J(x),x_{A_J(x)}).$$
--   A Boolean readout is $\mathcal F_J$-measurable exactly when it is constant on inputs with identical $\Phi_J$ values. Arity is the largest $|S|$ of an activation that is nonzero somewhere, default zero. The explicit cutoff predicate requires $J_S\equiv0$ for $|S|>d$. Define the load and active-union cost by
--   $$\Lambda_p(J)=\sum_S|S|\mathbb P_p[J_S(X_S)=1],\qquad M_p(J)=\mathbb E_p|A_J(X)|.$$
--   For $D\subseteq[n]$, forced activations are $J_S^D(z)=J_S(z^{D\cap S\leftarrow1})$. Their atoms always record original input labels, even when the active union changes. The ones-set of a cube point identifies an independent Bernoulli cube sample with the random subset $D$.
--
--   These definitions distinguish overlap counted with multiplicity from the union's cardinality, and adaptive information from dependence on a fixed coordinate subset.
-- source:
--   Chenghua Liu, Boning Meng, STOC 2027 submission #1509 (October 2026), Eq. (2), p. 2 (PDF p. 3); Eq. (3), p. 3 (PDF p. 4); Section 2, p. 4 (PDF p. 5); Section 3, p. 6 (PDF p. 7)

import Definitions.Def_NarrowDNF_Approx_Probability

namespace NarrowDNF.Approx

/-- Each activation takes exactly the labels in its own indexing set. -/
abbrev ActivationFamily (n : ℕ) := (S : Finset (Fin n)) → (S → Bool) → Bool

def IncreasingActivations {n : ℕ} (J : ActivationFamily n) : Prop :=
  ∀ S, Monotone (J S)

noncomputable def activeUnion {n : ℕ} (J : ActivationFamily n) (x : Cube n) :
    Finset (Fin n) := by
  classical
  exact (Finset.univ.filter (fun S => J S (fun i => x i) = true)).biUnion id

/-- A dependent pair records the active coordinates and their ORIGINAL input labels. -/
noncomputable def atom {n : ℕ} (J : ActivationFamily n) (x : Cube n) :
    Σ S : Finset (Fin n), S → Bool :=
  ⟨activeUnion J x, fun i => x i⟩

def AdaptiveMeasurable {n : ℕ} (J : ActivationFamily n) (v : Cube n → Bool) : Prop :=
  ∀ x y, atom J x = atom J y → v x = v y

noncomputable def arity {n : ℕ} (J : ActivationFamily n) : ℕ := by
  classical
  exact (Finset.univ.filter (fun S => ∃ z, J S z = true)).sup Finset.card

/-- Explicit vanishing above a natural arity cutoff, allowing d = 0. -/
def ArityLE {n : ℕ} (J : ActivationFamily n) (d : ℕ) : Prop :=
  ∀ S, d < S.card → ∀ z, J S z = false

/-- Multiplicity-counted load, not merely the expected active-union size. -/
noncomputable def load {n : ℕ} (p : ℝ) (J : ActivationFamily n) : ℝ :=
  ∑ S : Finset (Fin n), (S.card : ℝ) * prob p (fun x : Cube n => J S (fun i => x i) = true)

noncomputable def activeCost {n : ℕ} (p : ℝ) (J : ActivationFamily n) : ℝ :=
  expect p (fun x => (activeUnion J x).card)

/-- Force coordinates only inside the activation; the atom still records original labels. -/
def force {n : ℕ} (J : ActivationFamily n) (D : Finset (Fin n)) : ActivationFamily n :=
  fun S z => J S (fun i => if (i : Fin n) ∈ D then true else z i)

/-- Identify a random cube point with its random forcing subset. -/
def ones {n : ℕ} (x : Cube n) : Finset (Fin n) := Finset.univ.filter (fun i => x i = true)

end NarrowDNF.Approx


