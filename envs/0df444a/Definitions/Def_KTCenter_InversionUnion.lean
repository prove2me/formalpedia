-- Prove2me | Definitions.Def_KTCenter_InversionUnion
-- name    : KTCenter_InversionUnion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:27:35.727526+00:00
-- url     : https://prove2.me/theorems/eae00616-856e-4172-a83a-45d750d1c563
-- title:
--   Inversion sets $\mathrm{Inv}(\pi)$, unions $E_J$, degrees and movement allowances $w_v=5\deg_{E_J}(v)$
-- statement:
--   With the reference ranking $\rho=\pi_1$ relabeled to $(1,\dots,d)$, the **inversion set** of a ranking $\pi$ is $\mathrm{Inv}(\pi)=\{\{u,v\}:u<v,\ v\prec_\pi u\}$. For an index set $J\subseteq[n]$ let $E_J=\bigcup_{j\in J}\mathrm{Inv}(\pi_j)$. For a set $E$ of pairs, $N_E(v)=\{u:\{u,v\}\in E\}$ and $\deg_E(v)=|N_E(v)|$. The **movement allowance** of candidate $v$ is $w_v=5\deg_{E_J}(v)$ and $W=\sum_{v}w_v$. For an optimal center $\sigma^*$, $U_J=\mathrm{Inv}(\sigma^*)\setminus E_J$ collects the optimal inversions revealed by no selected input.
--
--   The allowances confine each candidate of a near-optimal ranking to an interval around its reference position (Lemma 4.1), and their sum controls every later additive error.
--
--   **Formalization Note** Pairs are ordered pairs $(u,v)$ with $u<v$ on 0-based labels. The function `lab v = v + 1` gives the 1-based label used in the arithmetic of §§4–6 (such as $v-w_v$ and $\lfloor (v-e)/H\rfloor$), as an integer.
-- source:
--   Chakraborty, Das, Mukherjee, Kendall–tau Center Admits a PTAS, STOC 2027 submission (manuscript sha256 4739ffba…), §3 p.14 (PDF p.16), §4 p.16 (PDF p.18), §4.2 p.17 (PDF p.19)

import Mathlib
import Definitions.Def_KTCenter_Instance

namespace KTCenter

/-- **Inversion set**, p.14 (PDF p.16): `Inv(π) = {{u, v} : u < v, v ≺_π u}`.

Chakraborty, Das, Mukherjee, *Kendall–tau Center Admits a PTAS*, STOC 2027 submission (manuscript
sha256 4739ffba…).

**Formalization Note.** The comparison `u < v` is on labels, that is, on positions in the reference
`ρ = (1, …, d)`. On relabeled inputs (`π₁ = 1`, §4.1) this is the source's `Inv`. An unordered pair
is the ordered pair `(u, v)` with `u < v`. -/
def Inv {d : ℕ} (π : Equiv.Perm (Fin d)) : Finset (Fin d × Fin d) :=
  Finset.univ.filter fun p => p.1 < p.2 ∧ π⁻¹ p.2 < π⁻¹ p.1

/-- `E_J = ⋃_{j∈J} Inv(π_j)`, p.16 (PDF p.18). -/
def EJ (I : Instance) (J : Finset (Fin I.n)) : Finset (Fin I.d × Fin I.d) :=
  J.biUnion fun j => Inv (I.π j)

/-- `deg_E(v) = |N_E(v)|`, p.14 (PDF p.16), for a set `E` of pairs `(u, v)` with `u < v`. -/
def deg {d : ℕ} (E : Finset (Fin d × Fin d)) (v : Fin d) : ℕ :=
  (Finset.univ.filter fun u : Fin d => (u, v) ∈ E ∨ (v, u) ∈ E).card

/-- The movement allowance `w_v = 5 deg_{E_J}(v)`, p.16 (PDF p.18). -/
def allowance (I : Instance) (J : Finset (Fin I.n)) (v : Fin I.d) : ℕ :=
  5 * deg (EJ I J) v

/-- `W = Σ_{v∈V} w_v` for arbitrary allowances, p.16 and p.27. -/
def totalW {d : ℕ} (w : Fin d → ℕ) : ℕ := ∑ v, w v

/-- `U_J = Inv(σ*) \ E_J`, p.17 (PDF p.19). -/
def UJ (I : Instance) (J : Finset (Fin I.n)) (σ : Equiv.Perm (Fin I.d)) :
    Finset (Fin I.d × Fin I.d) :=
  Inv σ \ EJ I J

/-- The 1-based label of a candidate, or the 1-based position of a 0-based position index.

**Formalization Note.** §§4–6 use the labels `1, …, d` in arithmetic such as `v − w_v`,
`⌊(v − e)/H⌋` and `clip_[1,d]`. Lean keeps these formulas as printed through `lab`, in `ℤ`. -/
def lab {d : ℕ} (v : Fin d) : ℤ := (v : ℤ) + 1

end KTCenter


