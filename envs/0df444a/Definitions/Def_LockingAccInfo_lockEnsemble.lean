-- Prove2me | Definitions.Def_LockingAccInfo_lockEnsemble
-- name    : LockingAccInfo_lockEnsemble
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:42:06.041197+00:00
-- url     : https://prove2.me/theorems/9a7186d8-dc85-4ca5-849a-23bbf779d7ed
-- title:
--   The {ccq}-state $\rho_{XYE}$ of §III and the derived $P_Y$ and $\mathcal N_y$
-- statement:
--   Let $X$ and $Y$ be random variables on $\mathcal X=\{0,1\}$ and $\mathcal Y=\{1,2,3\}^m$ with uniform joint distribution $P_{XY}(x,y)=\frac{1}{2\cdot3^m}$, and let $E$ be in the state $\rho_{E|(X,Y)=(x,y)}$ of Eq. (3) given $X=x$, $Y=y$. The **{ccq}-state** is
--
--   $$
--   \rho_{XYE}=\sum_{x,y}P_{XY}(x,y)\,|x,y\rangle\langle x,y|\otimes\rho_{E|(X,Y)=(x,y)} ,
--   $$
--
--   a classical-quantum ensemble with label $V=(X,Y)$. Two derived objects are used in the proof of Lemma 2: the marginal $P_Y(y)=\sum_xP_{XY}(x,y)$, and for each $y$ the binary family
--
--   $$
--   \mathcal N_y:=\{d\cdot P_{X|Y=y}(x)\cdot\rho_{E|(X,Y)=(x,y)}\}_{x\in\mathcal X},\qquad d=2^m,\quad P_{X|Y=y}(x)=P_{XY}(x,y)/P_Y(y).
--   $$
--
--   **Formalization Note** The ensemble is the published `CQData` (probabilities and conditional states). That $\mathcal N_y$ is a POVM is a consequence, not part of the definition.
-- source:
--   König, Renner, Bariska, Maurer, Locking of accessible information and implications for the security of quantum cryptography, arXiv:quant-ph/0512021v2, §III, p.2 (definition of X, Y, ρ_XYE) and p.3 (𝒩_y after Eq. (6))

import Mathlib
import Definitions.Def_LockingAccInfo_lockState
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P07

open QAlgorithms.Papers.Independent.Dependency50.P07 (CQData)

namespace LockingAccInfo

/-- König, Renner, Bariska, Maurer, arXiv:quant-ph/0512021v2, §III, p.2: "Let X and Y be random
variables on the binary set X := {0, 1} and the set of m-tuples Y := {1, 2, 3}^m, respectively,
such that the joint probability distribution PXY is uniform", with E in the state (3) given
X = x and Y = y. This is the {ccq}-state ρXYE, as a classical-quantum ensemble with classical
label V = (X, Y) (§II, p.2: ρVE = Σ_v PV(v)|v⟩⟨v| ⊗ ρE|V=v).

**Formalization Note.** The ensemble is the published `CQData` (probabilities `prob`,
conditional states `state`); `PXY(x, y) = 1/(2 · 3^m)`. -/
noncomputable def lockEnsemble (m : ℕ) : CQData (Bool × (Fin m → Fin 3)) (Fin m → Fin 2) where
  prob _ := ((2 : ℝ) * 3 ^ m)⁻¹
  state v := lockState v.1 v.2

/-- arXiv:quant-ph/0512021v2, §III, p.3: the marginal distribution PY(y) = Σ_x PXY(x, y) of Y
under the state (3) (uniform on {1, 2, 3}^m). -/
noncomputable def yMarginal (m : ℕ) (y : Fin m → Fin 3) : ℝ :=
  ∑ x, (lockEnsemble m).prob (x, y)

/-- arXiv:quant-ph/0512021v2, §III, after Eq. (6), p.3: for y ∈ Y the binary POVM
"Ny := {d · PX|Y=y(x) · ρE|(X,Y)=(x,y)}x∈X", with d := 2^m the dimension of E and
PX|Y=y(x) = PXY(x, y)/PY(y).

**Formalization Note.** The family is indexed by `x : Bool`; that it is a POVM is a consequence
stated in the theorems, not part of the definition. -/
noncomputable def lockBlockPOVM (m : ℕ) (y : Fin m → Fin 3) (x : Bool) :
    Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ :=
  (((2 : ℝ) ^ m * ((lockEnsemble m).prob (x, y) / yMarginal m y) : ℝ) : ℂ) • lockState x y

end LockingAccInfo


