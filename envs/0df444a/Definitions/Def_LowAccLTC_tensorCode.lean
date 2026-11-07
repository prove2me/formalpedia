-- Prove2me | Definitions.Def_LowAccLTC_tensorCode
-- name    : LowAccLTC_tensorCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:36:39.552558+00:00
-- url     : https://prove2.me/theorems/86ba4272-28a3-43ed-a2ae-5f67dc837b8d
-- title:
--   Tensor codes $B^{\otimes k}$, the hyperplane test, and HA local testability
-- statement:
--   Let $B\subseteq\mathbb F^n$ be a linear code. The **tensor code** $B^{\otimes k}\subseteq\mathbb F^{[n]^k}$ consists of the words whose restriction to every axis-parallel line lies in $B$. The **hyperplane test** samples a uniformly random direction $i\in[k]$ and value $a\in[n]$ and measures the distance of $f|_{x_i=a}$ from the local code $B^{\otimes(k-1)}$ of that hyperplane (words all of whose lines inside the hyperplane are in $B$); with uniform relative Hamming distances,
--   $$x(f)=\mathbb E_{i,a}\big[\mathrm{dist}(f|_{x_i=a},B^{\otimes(k-1)})\big].$$
--   $B^{\otimes k}$ is a **$(\nu_0,\psi)$-HA LTC** w.r.t. this test if $x(f)\le\nu_0$ implies $\mathrm{dist}(f,B^{\otimes k})\le\psi(x(f))$ for every $f$. $B$ **has relative distance at least $\Delta$** if distinct codewords differ on at least a $\Delta$-fraction of coordinates.
--
--   These are the objects of Theorem 5.5 [CMS17].
--
--   **Formalization Note** Only the HA LTC implication is bundled.
-- source:
--   Ben Yaacov, Dikstein, Liu, Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs (manuscript, sha256 04242e17…), Example 2.18 p.18 (PDF p.21), Definition 2.2 p.13 (PDF p.16), §5.1 pp.42–43 (PDF pp.45–46)

import Mathlib

namespace LowAccLTC

/-! Ben Yaacov, Dikstein, Liu, *Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs*,
unpublished manuscript (sha256 04242e17…); page references are printed pages (PDF page − 3). -/

variable {F : Type*} [Field F] {n : ℕ}

/-- Uniform relative Hamming distance of `f` and `g` on a finite set `S` of coordinates. -/
noncomputable def relHamming {α : Type*} (S : Finset α) (f g : α → F) : ℝ := by
  classical exact ((S.filter (fun x => f x ≠ g x)).card : ℝ) / S.card

/-- Uniform distance of `f` from a code `C` on the coordinates `S`, `min_{c ∈ C} dist_S(f, c)`
(§2.1, p.13), with the value `1` when `C = ∅` (as in `PartiteComplex.distTo`). -/
noncomputable def relDistTo {α : Type*} (S : Finset α) (f : α → F) (C : Set (α → F)) : ℝ :=
  sInf (insert 1 ((fun c => relHamming S f c) '' C))

/-- The tensor code `B^{⊗k} ⊆ F^{[n]^k}` (Example 2.18, p.18; §5.1, p.42): the words whose
restriction to every axis-parallel line lies in `B`. -/
def tensorCode (B : Submodule F (Fin n → F)) (k : ℕ) : Set ((Fin k → Fin n) → F) :=
  {f | ∀ (x : Fin k → Fin n) (i : Fin k), (fun a => f (Function.update x i a)) ∈ B}

/-- The axis-parallel hyperplane `{x : x_i = a}` of `[n]^k`. -/
noncomputable def hyperplane {k : ℕ} (i : Fin k) (a : Fin n) : Finset (Fin k → Fin n) :=
  Finset.univ.filter (fun x => x i = a)

/-- The local code `B^{⊗(k-1)}` on the hyperplane `x_i = a` (§3.2, p.25; §5.1, p.43): words
whose restriction to every axis-parallel line inside the hyperplane (direction `l ≠ i`) lies in
`B`. -/
def hyperplaneLocalCode (B : Submodule F (Fin n → F)) {k : ℕ} (i : Fin k) (a : Fin n) :
    Set ((Fin k → Fin n) → F) :=
  {h | ∀ x : Fin k → Fin n, x i = a → ∀ l, l ≠ i → (fun b => h (Function.update x l b)) ∈ B}

/-- The hyperplane-test quantity `E_{i,a}[dist(f|_{x_i = a}, B^{⊗(k-1)})]` (§5.1, p.43): `i` and
`a` are uniform. -/
noncomputable def hyperplaneTestDist (B : Submodule F (Fin n → F)) {k : ℕ}
    (f : (Fin k → Fin n) → F) : ℝ :=
  (∑ ia : Fin k × Fin n, relDistTo (hyperplane ia.1 ia.2) f (hyperplaneLocalCode B ia.1 ia.2)) /
    (Fintype.card (Fin k × Fin n) : ℝ)

/-- `B^{⊗k}` is a `(ν₀, ψ)`-HA LTC (high acceptance locally testable code) w.r.t. the hyperplane
test (Definition 2.2, p.13): `x := E_{i,a}[dist(f|_{x_i = a}, B^{⊗(k-1)})] ≤ ν₀` implies
`dist(f, B^{⊗k}) ≤ ψ(x)`. Only the implication is bundled. -/
def IsHALTCHyperplane (B : Submodule F (Fin n → F)) (k : ℕ) (ν₀ : ℝ) (ψ : ℝ → ℝ) : Prop :=
  ∀ f : (Fin k → Fin n) → F, hyperplaneTestDist B f ≤ ν₀ →
    relDistTo Finset.univ f (tensorCode B k) ≤ ψ (hyperplaneTestDist B f)

/-- `B` has relative distance at least `Δ`: distinct codewords differ on at least a
`Δ`-fraction of the coordinates. -/
def HasRelDistAtLeast (B : Submodule F (Fin n → F)) (Δ : ℝ) : Prop :=
  ∀ c ∈ B, ∀ c' ∈ B, c ≠ c' → Δ ≤ relHamming Finset.univ c c'

end LowAccLTC


