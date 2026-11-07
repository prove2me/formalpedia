-- Prove2me | Definitions.Def_RegevRecon_GibbsState
-- name    : RegevRecon_GibbsState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:03:54.515938+00:00
-- url     : https://prove2.me/theorems/bdac33bd-7cd5-4f66-9ddb-d80d65a1f861
-- title:
--   The energy $E(x)$ and the Gibbs distribution $\Pr_\beta(x)$ of a max-LINSAT instance
-- statement:
--   A max-LINSAT instance is a matrix $B\in\mathbb F_p^{m\times n}$ with sets $F_1,\dots,F_m\subseteq\mathbb F_p$. Its **energy** is the number of violated constraints,
--
--   $$
--   E(x)=\Bigl|\Bigl\{i:\sum_{j=1}^nB_{ij}x_j\notin F_i\Bigr\}\Bigr|,
--   $$
--
--   and its **Gibbs distribution** is $\Pr_\beta(x)=e^{-\beta E(x)}/Z$ with $Z=\sum_xe^{-\beta E(x)}$. The coherent Gibbs state is $|\psi_\beta\rangle=\sum_x\sqrt{\Pr_\beta(x)}\,|x\rangle$. For the ensemble, $F_j=\tau_j+S$.
-- source:
--   Jordan, Nguyen, Zhou, Regev's Reduction Reaches Reconstruction, STOC 2027 submission (manuscript sha256 9f861d6a…), (1)–(3), pp.2–3; Definition 1, p.3; Definition 2, p.4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_DQI
import Definitions.Def_RegevRecon_Messages

namespace RegevRecon

open Finset

variable {p m n : ℕ} [Fact p.Prime]

/-- The target sets `F_j = τ_j + S` (Definition 2, p.4). -/
def targetSets (S : Finset (ZMod p)) (τ : Fin m → ZMod p) : Fin m → Finset (ZMod p) :=
  fun j => S.image (τ j + ·)

/-- **The energy** `E(x) = |{i : Σ_j B_ij x_j ∉ F_i}|`, Jordan, Nguyen, Zhou, *Regev's Reduction Reaches Reconstruction*, STOC 2027 submission (manuscript sha256 9f861d6a…), (3), p.3: the number of violated
constraints, `m` minus the published count of satisfied constraints. -/
def energy (B : Matrix (Fin m) (Fin n) (ZMod p)) (F : Fin m → Finset (ZMod p))
    (x : Fin n → ZMod p) : ℕ :=
  m - QAlgorithms.linsatSatisfied B F x

/-- **The Gibbs distribution** `Pr_β(x) = e^{−βE(x)}/Z`, `Z = Σ_x e^{−βE(x)}`, (1), p.2. The amplitudes
of the coherent Gibbs state `|ψ_β⟩ = Σ_x √Pr_β(x) |x⟩` of (2) are `√Pr_β(x)`. -/
noncomputable def gibbsProb (B : Matrix (Fin m) (Fin n) (ZMod p)) (F : Fin m → Finset (ZMod p))
    (β : ℝ) (x : Fin n → ZMod p) : ℝ :=
  Real.exp (-β * energy B F x) / ∑ y, Real.exp (-β * energy B F y)

end RegevRecon


