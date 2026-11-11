-- Prove2me | Definitions.Def_KeySchedules_Iterative_Schedule
-- name    : KeySchedules_Iterative_Schedule
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T22:50:11.859078+00:00
-- url     : https://prove2.me/theorems/00bcef48-4915-4f30-87f1-4fe4a9e5c373
-- title:
--   The iterative key schedule KS_φ, state paths, X, μ, α, good tuples, F(θ) and the image-exchange procedure
-- statement:
--   Let $G$ be a finite abelian group, $S$ a nonempty finite set and $r\ge1$. A map $\mathrm{Out}:S\to G$ is **balanced** when $|\mathrm{Out}^{-1}(k)|\cdot|G|=|S|$ for every $k\in G$. For a permutation $\varphi$ of $S$ the **state path** of a master key $s$ is $\mathrm{Path}_\varphi(s)=(\varphi(s),\varphi^2(s),\dots,\varphi^r(s))\in S^r$, and the **iterative key schedule** (Definition 2.2 with $\varphi_1=\dots=\varphi_r=\varphi$, Eq. (8)) is
--   $$\mathrm{KS}_\varphi(s)=\bigl(\mathrm{Out}(\varphi(s)),\mathrm{Out}(\varphi^2(s)),\dots,\mathrm{Out}(\varphi^r(s))\bigr)\in G^r .$$
--   For $h:G^r\to[0,1]$ and $z\in S^r$, $\tilde h(z)=h(\mathrm{Out}(z_1),\dots,\mathrm{Out}(z_r))$, $X(\varphi)=\mathbb E_{s\leftarrow S}h(\mathrm{KS}_\varphi(s))$, $\mu=\mathbb E_\varphi X(\varphi)$, $\alpha=\mathbb E_{k\leftarrow G^r}h(k)$, $F(\theta)=\mathbb E_\varphi e^{\theta X(\varphi)}$, and $\mathbb E[e^{\theta X}\mid E_{s,z}]$ is the average of $e^{\theta X(\varphi)}$ over the event $E_{s,z}=\{\varphi:\mathrm{Path}_\varphi(s)=z\}$; $\varphi$ is uniform on the permutations of $S$.
--
--   A candidate path $z$ from $s$ requires the inputs $a_1=s$, $a_i=z_{i-1}$ ($2\le i\le r$); $z$ is **good** when the $a_i$ are pairwise distinct and the $z_i$ are pairwise distinct. The event $E_{s,z}$ imposes the constraints $\varphi(a_i)=z_i$; with repetitions removed they form the list $\varphi(a_j)=b_j$. The **image-exchange procedure** enforces them one at a time: to enforce $\varphi(a_j)=b_j$ it takes $x=\varphi^{-1}(b_j)$ and exchanges the images at $a_j$ and $x$, i.e. $\varphi\mapsto\varphi\circ(a_j\ x)$ (no change when $x=a_j$).
--
--   **Formalization Note.** Round indices are `Fin r`: index $i$ holds round $i+1$. Uniform probabilities over permutations are averages over the finite type `Equiv.Perm S`.
-- source:
--   Beierle, Choi, Hhan, Jha, Kim, Minimizing Key Schedules for Key-Alternating Ciphers, STOC 2027 submission (manuscript sha256 cd9f815b…), p. 7, Definition 2.2; p. 11, Eq. (8) and the proof of Lemma 3.2 (Path_φ, h̃, X, μ, α, good tuples); p. 12, Step 2; p. 13, Step 3

import Mathlib

namespace KeySchedules.Iterative

/-!
# The iterative key schedule `KS_φ`, state paths, and the objects of the proof of Lemma 3.2

Beierle, Choi, Hhan, Jha, Kim, *Minimizing Key Schedules for Key-Alternating Ciphers*,
STOC 2027 submission (manuscript sha256 cd9f815b…), Definition 2.2 (p. 7), Eq. (8) (p. 11),
and the proof of Lemma 3.2 (pp. 11–13): `Path_φ`, `h̃`, `X`, `μ`, `α`, good tuples (Step 1),
the constraints of the event `E_{s,z}` and the image-exchange procedure (Step 2),
`F(θ) = E e^{θX}` and `E[e^{θX} | E_{s,z}]` (Step 3).

* `S` is the master-key space, `G` the group of round keys, `Out : S → G` the balanced output
  map, `r` the number of rounds. Round keys are indexed by `Fin r`: index `i` is the paper's
  round `i + 1`.
* `φ` ranges over `Equiv.Perm S`; "uniform `φ`" is the uniform distribution on this finite
  set, so `Pr_φ`/`E_φ` are averages over `Equiv.Perm S`.
-/

/-- `Out` is balanced: `|Out⁻¹(k)| · |G| = |S|` for every `k ∈ G`, i.e. `|Out⁻¹(k)| = |S|/|G|`
(this forces `|G| ∣ |S|`). -/
def IsBalanced {S G : Type} [Fintype S] [Fintype G] (Out : S → G) : Prop :=
  ∀ k : G, (Out ⁻¹' {k}).ncard * Fintype.card G = Fintype.card S

/-- The state path `Path_φ(s) = (φ(s), φ²(s), …, φ^r(s)) ∈ S^r`; index `i : Fin r` holds
`φ^{i+1}(s)`. -/
def statePath {S : Type} (φ : Equiv.Perm S) (r : ℕ) (s : S) : Fin r → S :=
  fun i => (φ ^ (i.val + 1)) s

/-- The iterative key schedule with one permutation (Definition 2.2 with `φ_1 = ⋯ = φ_r = φ`,
Eq. (8)): `KS_φ(s) = (Out(φ(s)), Out(φ²(s)), …, Out(φ^r(s)))`. The state `x_0 = s` is not
output. -/
def KS {S G : Type} (Out : S → G) (r : ℕ) (φ : Equiv.Perm S) (s : S) : Fin r → G :=
  fun i => Out (statePath φ r s i)

/-- `h̃(z) = h(Out(z_1), …, Out(z_r))` for `z ∈ S^r`. -/
def htilde {S G : Type} {r : ℕ} (Out : S → G) (h : (Fin r → G) → ℝ) (z : Fin r → S) : ℝ :=
  h (fun i => Out (z i))

/-- The inputs to `φ` required by a candidate state path `z` from the master key `s`:
`a_1 = s`, `a_i = z_{i−1}` (`2 ≤ i ≤ r`). In `Fin r`: index `0` is `s`, index `i ≥ 1` is
`z (i − 1)`. -/
def pathInputs {S : Type} {r : ℕ} (s : S) (z : Fin r → S) : Fin r → S :=
  fun i => if hi : i.val = 0 then s else z ⟨i.val - 1, by omega⟩

/-- `z` is good (Step 1 of the proof of Lemma 3.2): the inputs `a_i` are pairwise distinct
and the `z_i` are pairwise distinct. -/
def IsGood {S : Type} {r : ℕ} (s : S) (z : Fin r → S) : Prop :=
  Function.Injective (pathInputs s z) ∧ Function.Injective z

/-- `X(φ) = E_{s←S}[h(KS_φ(s))]`. -/
noncomputable def avgX {S G : Type} [Fintype S] {r : ℕ} (Out : S → G) (h : (Fin r → G) → ℝ)
    (φ : Equiv.Perm S) : ℝ :=
  (Fintype.card S : ℝ)⁻¹ * ∑ s : S, h (KS Out r φ s)

/-- `μ = E_φ X(φ)` for `φ` uniform on the permutations of `S`. -/
noncomputable def meanMu {S G : Type} [Fintype S] [DecidableEq S] {r : ℕ} (Out : S → G)
    (h : (Fin r → G) → ℝ) : ℝ :=
  (Fintype.card (Equiv.Perm S) : ℝ)⁻¹ * ∑ φ : Equiv.Perm S, avgX Out h φ

/-- `α = E_{k←G^r} h(k)`. -/
noncomputable def alphaMean {G : Type} [Fintype G] {r : ℕ} (h : (Fin r → G) → ℝ) : ℝ :=
  (Fintype.card (Fin r → G) : ℝ)⁻¹ * ∑ k : Fin r → G, h k

/-- `F(θ) = E_φ e^{θ X(φ)}`. -/
noncomputable def mgfF {S G : Type} [Fintype S] [DecidableEq S] {r : ℕ} (Out : S → G)
    (h : (Fin r → G) → ℝ) (θ : ℝ) : ℝ :=
  (Fintype.card (Equiv.Perm S) : ℝ)⁻¹ * ∑ φ : Equiv.Perm S, Real.exp (θ * avgX Out h φ)

/-- `E[e^{θX} | E_{s,z}]` for the event `E_{s,z} = {Path_φ(s) = z}`: the average of
`e^{θ X(φ)}` over the permutations in `E_{s,z}`. -/
noncomputable def condMgf {S G : Type} [Fintype S] [DecidableEq S] {r : ℕ} (Out : S → G)
    (h : (Fin r → G) → ℝ) (s : S) (z : Fin r → S) (θ : ℝ) : ℝ :=
  (∑ᶠ φ ∈ {φ : Equiv.Perm S | statePath φ r s = z}, Real.exp (θ * avgX Out h φ)) /
    ({φ : Equiv.Perm S | statePath φ r s = z}.ncard : ℝ)

/-- The constraints `φ(a_i) = z_i` (`1 ≤ i ≤ r`) imposed by the event `E_{s,z}`, as pairs
`(a_i, z_i)` in the order `i = 1, …, r`, with repeated constraints removed. -/
def constraints {S : Type} [DecidableEq S] {r : ℕ} (s : S) (z : Fin r → S) : List (S × S) :=
  ((List.finRange r).map (fun i => (pathInputs s z i, z i))).dedup

/-- One image exchange enforcing `φ(a) = b`: with `x = φ⁻¹(b)`, exchange the images at `a` and
`x`, i.e. `φ ↦ φ ∘ (a x)`. If `x = a` nothing changes. -/
def exchangeStep {S : Type} [DecidableEq S] (φ : Equiv.Perm S) (c : S × S) : Equiv.Perm S :=
  φ * Equiv.swap c.1 (φ.symm c.2)

/-- The image-exchange procedure of Step 2: enforce the constraints of `E_{s,z}` one at a time,
in order. -/
def exchange {S : Type} [DecidableEq S] {r : ℕ} (s : S) (z : Fin r → S) (φ : Equiv.Perm S) :
    Equiv.Perm S :=
  (constraints s z).foldl exchangeStep φ

end KeySchedules.Iterative


