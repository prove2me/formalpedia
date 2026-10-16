-- Prove2me | Definitions.Def_DQI_Imperfect_Setting
-- name    : DQI_Imperfect_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T11:02:42.099285+00:00
-- url     : https://prove2.me/theorems/c454dc2a-2932-4ddc-ab34-166136b804d2
-- title:
--   Max-XORSAT and imperfect-decoder DQI model
-- statement:
--   Let $B\in\mathbb F_2^{m\times n}$ be a binary matrix and let $v\in\mathbb F_2^m$ be a vector of signs. A binary word $y\in\mathbb F_2^m$ has Hamming weight $|y|$, and $E_k$ is the shell of words with $|y|=k$. A deterministic decoder $\mathrm{dec}:\mathbb F_2^n\to\mathbb F_2^m$ takes a syndrome $B^\top y$ to an error guess. The correctly decoded words of weight $k$ form $D_k=\{y\in E_k: \mathrm{dec}(B^\top y)=y\}$; the remaining words form $F_k$. Their failure fractions are $\varepsilon_k=|F_k|/\binom m k$ and $\varepsilon=\max_{0\le k\le\ell}\varepsilon_k$.
--
--   The file defines the max-XORSAT objective, the ideal syndrome state (140), the postselected state (171), the binary Hadamard transform, and the objective expectation in a normalized state. It also defines the matrices $\bar A^{(m,\ell)}$, $\bar A^{(m,\ell,D)}$, $E^{(m,\ell,F)}$, and $A^{(m,\ell,d)}$ from (147), (177), (181), and (70). These objects provide the common setting for the theorem and its seven supporting results.
--
--   **Formalization Note** Coordinates use zero-based `Fin` indices. Vectors are functions into `ZMod 2`; amplitudes and weights are real. The decoder is one fixed function of the syndrome and does not depend on $v$. The expectation divides by the squared norm, so theorem statements require a positive norm when normalization matters.
-- source:
--   Jordan et al., Optimization by Decoded Quantum Interferometry, arXiv:2408.08292v5, pp. 17–19, 27, 35–41, (18)–(28), (70), (140), (147)–(148), (171), (177)–(178), (181)–(182)

import Mathlib
import Definitions.Def_DQI_Semicircle_Setting

namespace DQI.Imperfect

/-- The real character of the binary field. -/
def sgn (a : ZMod 2) : ℝ := if a = 0 then 1 else -1

/-- The number of nonzero coordinates of a binary word. -/
def wt {m : ℕ} (y : Fin m → ZMod 2) : ℕ :=
  (Finset.univ.filter (fun i => y i ≠ 0)).card

/-- The binary Hamming shell of weight `k`. -/
def shell (m k : ℕ) : Finset (Fin m → ZMod 2) :=
  Finset.univ.filter (fun y => wt y = k)

/-- The max-XORSAT objective in equation (18). -/
def obj {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2))
    (v : Fin m → ZMod 2) (x : Fin n → ZMod 2) : ℝ :=
  ∑ i, sgn ((B.mulVec x) i + v i)

/-- Errors decoded correctly from their syndrome, in shell `k`. -/
def Dset {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2))
    (dec : (Fin n → ZMod 2) → (Fin m → ZMod 2)) (k : ℕ) :
    Finset (Fin m → ZMod 2) :=
  (shell m k).filter (fun y => dec (B.transpose.mulVec y) = y)

/-- Errors decoded incorrectly from their syndrome, in shell `k`. -/
def Fset {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2))
    (dec : (Fin n → ZMod 2) → (Fin m → ZMod 2)) (k : ℕ) :
    Finset (Fin m → ZMod 2) :=
  (shell m k).filter (fun y => dec (B.transpose.mulVec y) ≠ y)

/-- The fraction of weight-`k` errors misidentified by the decoder. -/
noncomputable def epsk {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2))
    (dec : (Fin n → ZMod 2) → (Fin m → ZMod 2)) (k : ℕ) : ℝ :=
  (Fset B dec k).card / (Nat.choose m k : ℝ)

/-- The worst failure rate among weights zero through `ℓ`. -/
noncomputable def epsMax {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2))
    (dec : (Fin n → ZMod 2) → (Fin m → ZMod 2)) (ℓ : ℕ) : ℝ :=
  (Finset.range (ℓ + 1)).sup' (by simp) (epsk B dec)

/-- The ideal, unnormalized syndrome-space state in equation (140). -/
noncomputable def Pt {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2))
    (v : Fin m → ZMod 2) (ℓ : ℕ) (w : Fin (ℓ + 1) → ℝ)
    (s : Fin n → ZMod 2) : ℝ :=
  ∑ k : Fin (ℓ + 1),
    (w k / Real.sqrt (Nat.choose m k.val : ℝ)) *
      ∑ y ∈ (shell m k.val).filter (fun y => B.transpose.mulVec y = s),
        sgn (v ⬝ᵥ y)

/-- The postselected, unnormalized syndrome-space state in equation (171). -/
noncomputable def PtD {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2))
    (v : Fin m → ZMod 2)
    (dec : (Fin n → ZMod 2) → (Fin m → ZMod 2))
    (ℓ : ℕ) (w : Fin (ℓ + 1) → ℝ) (s : Fin n → ZMod 2) : ℝ :=
  ∑ k : Fin (ℓ + 1),
    (w k / Real.sqrt (Nat.choose m k.val : ℝ)) *
      ∑ y ∈ (Dset B dec k.val).filter (fun y => B.transpose.mulVec y = s),
        sgn (v ⬝ᵥ y)

/-- The normalized tensor-power binary Hadamard transform. -/
noncomputable def hadamard {n : ℕ} (ψ : (Fin n → ZMod 2) → ℝ)
    (x : Fin n → ZMod 2) : ℝ :=
  (1 / Real.sqrt ((2 : ℝ) ^ n)) * ∑ s, sgn (s ⬝ᵥ x) * ψ s

/-- Expected objective in the normalized state of amplitudes `ψ`. -/
noncomputable def expObj {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2))
    (v : Fin m → ZMod 2) (ψ : (Fin n → ZMod 2) → ℝ) : ℝ :=
  (∑ x, ψ x ^ 2 * obj B v x) / (∑ x, ψ x ^ 2)

/-- The matrix in equations (147)–(148). -/
noncomputable def Abar {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2))
    (v : Fin m → ZMod 2) (ℓ : ℕ) :
    Matrix (Fin (ℓ + 1)) (Fin (ℓ + 1)) ℝ :=
  fun k k' =>
    (1 / Real.sqrt ((Nat.choose m k.val : ℝ) * (Nat.choose m k'.val : ℝ))) *
      ∑ i : Fin m,
        ∑ yy ∈ ((shell m k.val) ×ˢ (shell m k'.val)).filter
            (fun yy => B.transpose.mulVec (yy.1 + yy.2 + Pi.single i 1) = 0),
          sgn (v i + v ⬝ᵥ (yy.1 + yy.2))

/-- The imperfect-decoder matrix in equations (177)–(178). -/
noncomputable def AbarD {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2))
    (v : Fin m → ZMod 2)
    (dec : (Fin n → ZMod 2) → (Fin m → ZMod 2)) (ℓ : ℕ) :
    Matrix (Fin (ℓ + 1)) (Fin (ℓ + 1)) ℝ :=
  fun k k' =>
    (1 / Real.sqrt ((Nat.choose m k.val : ℝ) * (Nat.choose m k'.val : ℝ))) *
      ∑ i : Fin m,
        ∑ yy ∈ ((Dset B dec k.val) ×ˢ (Dset B dec k'.val)).filter
            (fun yy => B.transpose.mulVec (yy.1 + yy.2 + Pi.single i 1) = 0),
          sgn (v i + v ⬝ᵥ (yy.1 + yy.2))

/-- The matrix in equations (181)–(182). -/
noncomputable def Emat {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2))
    (dec : (Fin n → ZMod 2) → (Fin m → ZMod 2)) (ℓ : ℕ) :
    Matrix (Fin (ℓ + 1)) (Fin (ℓ + 1)) ℝ :=
  fun k k' =>
    (1 / Real.sqrt ((Nat.choose m k.val : ℝ) * (Nat.choose m k'.val : ℝ))) *
      ∑ i : Fin m,
        ((((shell m k.val) ×ˢ (Fset B dec k'.val)) ∪
          ((Fset B dec k.val) ×ˢ (shell m k'.val))).filter
          (fun yy => yy.1 + yy.2 + Pi.single i 1 = 0)).card

/-- Uniform expectation over the binary phase vector. -/
noncomputable def avgV (m : ℕ) (g : (Fin m → ZMod 2) → ℝ) : ℝ :=
  (1 / ((2 : ℝ) ^ m)) * ∑ v, g v

end DQI.Imperfect


