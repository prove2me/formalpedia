-- Prove2me | Definitions.Def_IntMul_HvdH_FPApprox
-- name    : IntMul_HvdH_FPApprox
-- status  : Definition
-- author  : @xuanji
-- created : 2026-10-12T00:49:18.897983+00:00
-- url     : https://prove2.me/theorems/ec736520-67f6-4dfd-acea-9d11fead4002
-- title:
--   Fixed-point numerical approximations of linear maps on Gaussian-integer arrays (Harvey–van der Hoeven §2.6–2.7)
-- statement:
--   Fixed-point arrays and their error calculus, following Harvey–van der Hoeven §2.6–2.7. At precision $p$, an array $U:\iota\to\mathbb Z[i]$ stands for $2^{-p}U:\iota\to\mathbb C$.
--
--   * `gC z` is the Gaussian integer $z=(a,b)$ viewed as $a+bi\in\mathbb C$.
--   * `InDisc p U` means every entry satisfies $|U_i|\le2^p$, i.e. $2^{-p}U$ lies in the closed unit polydisc $\tilde{\mathbb C}^\circ$.
--   * `FPApprox p Ã A ε` says that $\tilde A$ maps the polydisc to itself and $|\tilde A(U)_k-2^pA(2^{-p}U)_k|\le\varepsilon$ for every such $U$. This is the paper's $\varepsilon(\tilde A)\le\varepsilon$.
--   * `SupLip A` means $A$ is $1$-Lipschitz for the sup norm. For linear maps this is $\|A\|\le1$.
--   * `sliceMapZ`, `sliceCompZ` and `tensorMapZ` apply one-dimensional integer maps slice by slice to $d$-dimensional arrays. They mirror `sliceMap`, `sliceComp` and `tensorMap` from `IntMul_HvdH_SliceTensor`.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, §2.6–2.7

import Definitions.Def_IntMul_HvdH_SliceTensor

/-! Fixed-point numerical approximations of linear maps (Harvey–van der Hoeven §2.6–2.7) on
arrays of Gaussian integers `(re, im) : ℤ × ℤ`. At precision `p`, an array `U : ι → ℤ × ℤ`
stands for `2^{-p} U : ι → ℂ`. -/

namespace IntMul.HvdH

/-- A Gaussian integer as a complex number. -/
noncomputable def gC (z : ℤ × ℤ) : ℂ := (z.1 : ℂ) + (z.2 : ℂ) * Complex.I

/-- `2^{-p} U` lies in the closed unit polydisc. -/
def InDisc {ι : Type*} (p : ℕ) (U : ι → ℤ × ℤ) : Prop := ∀ i, ‖gC (U i)‖ ≤ 2 ^ p

/-- `Aa` is a numerical approximation of `A` at precision `p` with error `ε`: it maps the unit
polydisc to itself, and `|Aa U - 2^p A(2^{-p} U)| ≤ ε` entrywise. -/
def FPApprox {ι κ : Type*} (p : ℕ) (Aa : (ι → ℤ × ℤ) → (κ → ℤ × ℤ)) (A : (ι → ℂ) → (κ → ℂ))
    (ε : ℝ) : Prop :=
  ∀ U, InDisc p U → InDisc p (Aa U) ∧
    ∀ k, ‖gC (Aa U k) - 2 ^ p * A (fun i => gC (U i) / 2 ^ p) k‖ ≤ ε

/-- `A` is `1`-Lipschitz for the sup norm. -/
def SupLip {ι κ : Type*} (A : (ι → ℂ) → (κ → ℂ)) : Prop :=
  ∀ (x y : ι → ℂ) (δ : ℝ), (∀ i, ‖x i - y i‖ ≤ δ) → ∀ k, ‖A x k - A y k‖ ≤ δ

/-- Apply a one-dimensional map `A` to every `i`-slice of a `d`-dimensional array of Gaussian
integers. -/
def sliceMapZ {d : ℕ} (i : Fin d) (A : (ℕ → ℤ × ℤ) → (ℕ → ℤ × ℤ)) (x : (Fin d → ℕ) → ℤ × ℤ) :
    (Fin d → ℕ) → ℤ × ℤ :=
  fun j => A (fun k => x (Function.update j i k)) (j i)

/-- Apply the maps `A i` slice by slice, for the axes listed in `l`, first axis first. -/
def sliceCompZ {d : ℕ} (A : Fin d → (ℕ → ℤ × ℤ) → (ℕ → ℤ × ℤ)) :
    List (Fin d) → ((Fin d → ℕ) → ℤ × ℤ) → ((Fin d → ℕ) → ℤ × ℤ)
  | [] => id
  | i :: l => sliceCompZ A l ∘ sliceMapZ i (A i)

/-- The fixed-point tensor product `⊗ᵢ Ãᵢ` (Lemma 2.11). -/
def tensorMapZ {d : ℕ} (A : Fin d → (ℕ → ℤ × ℤ) → (ℕ → ℤ × ℤ)) :
    ((Fin d → ℕ) → ℤ × ℤ) → ((Fin d → ℕ) → ℤ × ℤ) :=
  sliceCompZ A (List.finRange d)

end IntMul.HvdH


