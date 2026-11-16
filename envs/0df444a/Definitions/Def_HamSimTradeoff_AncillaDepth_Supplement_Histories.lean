-- Prove2me | Definitions.Def_HamSimTradeoff_AncillaDepth_Supplement_Histories
-- name    : HamSimTradeoff_AncillaDepth_Supplement_Histories
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:48:02.12695+00:00
-- url     : https://prove2.me/theorems/88a11564-e6ce-49f3-a7d1-3b5f15553b2a
-- title:
--   Canonical query histories and their homogeneous components
-- statement:
--   Use the canonical histories from the proof of Lemma 5.2: $W_j=V_{j-1}\cdots V_0$, $\psi_j=W_j^\dagger|0^a\rangle$, $u=W_{T+1}^\dagger|0^a\rangle$, $v=|0^a\rangle$, $\Pi_j=|\psi_j\rangle\langle\psi_j|$, $A_j=I-\Pi_j$. The amplitudes $x_j,y_j,h_{ij}$ are those of (5.4), $H_{ij}=h_{ij}$ for $i>j$ and zero otherwise, and $G$ is their Gram matrix. All objects are computed from the circuit's controllers. The half-open zero-based interval product $A_{h-1}\cdots A_l$ fixes every boundary convention. The path coefficient is the scalar compression of the ordered product in which positions in $S$ use $\Pi_j$ and all others use $A_j$; this is the direct expansion of (5.3). Then
--   $$B_r(P)=\sum_{|S|=r}\alpha_S P_{\alpha_{t_r}}\cdots P_{\alpha_{t_1}}.$$
--   The word coefficient sums $\alpha_S$ over identical words; the endpoint matrix sums over paths with the specified first and last labels. The layer also defines $c_j,\beta_j,\gamma_j,s_j$ of Lemma 5.6, the Frobenius norm and rectangular isometries $U^\dagger U=I$. No contraction, rank or approximation bound is bundled into a definition.
-- source:
--   Yuxin Zhang, Changpeng Shao, STOC 2027 submission #334 (October 2026), pp. 24–28, Eqs. (5.3)–(5.7), Lemmas 5.6–5.8

import Definitions.Def_HamSimTradeoff_AncillaDepth_Supplement_LCU
open scoped BigOperators Matrix.Norms.L2Operator

namespace HamSimTradeoff.AncillaDepth.Supplement
noncomputable section

def braKet {n : ℕ} (u v : Fin n → ℂ) : ℂ := ∑ i, star (u i) * v i

def vecNormSq {n : ℕ} (v : Fin n → ℂ) : ℝ := ∑ i, ‖v i‖^2

def frobenius {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℂ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, ‖A i j‖^2)

/-- W_{t+1}, with query positions t indexed from zero. -/
def prefixController {L : ℕ} (B : LCUCircuit L) (n : ℕ) : Mat (2 ^ B.a) :=
  (((List.finRange (B.T + 1)).filter (fun j => j.val < n)).reverse.map
    (fun j => (B.V j : Mat (2 ^ B.a)))).prod

def psi {L : ℕ} (B : LCUCircuit L) (t : Fin B.T) : Fin (2 ^ B.a) → ℂ :=
  fun i => star (prefixController B (t.val+1) (ancillaZero B.a) i)

def historyU {L : ℕ} (B : LCUCircuit L) : Fin (2 ^ B.a) → ℂ :=
  fun i => star (prefixController B (B.T+1) (ancillaZero B.a) i)

def historyV {L : ℕ} (B : LCUCircuit L) : Fin (2 ^ B.a) → ℂ :=
  fun i => if i = ancillaZero B.a then 1 else 0

def projector {L : ℕ} (B : LCUCircuit L) (t : Fin B.T) : Mat (2 ^ B.a) :=
  fun i j => psi B t i * star (psi B t j)

def complement {L : ℕ} (B : LCUCircuit L) (t : Fin B.T) : Mat (2 ^ B.a) :=
  1 - projector B t

/-- A_{hi-1} ... A_lo; half-open, zero-based interval. -/
def historyProduct {L : ℕ} (B : LCUCircuit L) (lo hi : ℕ) : Mat (2 ^ B.a) :=
  (((List.finRange B.T).filter (fun t => lo ≤ t.val ∧ t.val < hi)).reverse.map
    (complement B)).prod

def historyX {L : ℕ} (B : LCUCircuit L) (t : Fin B.T) : ℂ :=
  braKet (historyU B) ((historyProduct B (t.val+1) B.T).mulVec (psi B t))

def historyY {L : ℕ} (B : LCUCircuit L) (t : Fin B.T) : ℂ :=
  braKet (psi B t) ((historyProduct B 0 t.val).mulVec (historyV B))

def historyH {L : ℕ} (B : LCUCircuit L) : Mat B.T :=
  fun i j => if j < i then braKet (psi B i)
    ((historyProduct B (j.val+1) i.val).mulVec (psi B j)) else 0

def gram {L : ℕ} (B : LCUCircuit L) : Mat B.T :=
  fun i j => braKet (psi B i) (psi B j)

/-- Direct projector expansion of alpha_S in (5.5), also for the empty path. -/
def pathAmplitude {L : ℕ} (B : LCUCircuit L) (S : Finset (Fin B.T)) : ℂ :=
  braKet (historyU B) ((((List.finRange B.T).reverse.map
    (fun t => if t ∈ S then projector B t else complement B t)).prod).mulVec (historyV B))

def pathWord {L : ℕ} (B : LCUCircuit L) (S : Finset (Fin B.T)) : List (Fin L) :=
  (S.sort (· ≤ ·)).map B.query

def wordCoefficient {L : ℕ} (B : LCUCircuit L) (w : List (Fin L)) : ℂ :=
  ∑ S : Finset (Fin B.T), if pathWord B S = w then pathAmplitude B S else 0

def homogeneous {L N : ℕ} (B : LCUCircuit L) (r : ℕ) (P : Fin L → Mat N) : Mat N :=
  ∑ S : Finset (Fin B.T), if S.card = r then
    pathAmplitude B S • (((pathWord B S).reverse.map P).prod) else 0

def endpointMatrix {L : ℕ} (B : LCUCircuit L) (r : ℕ) : Mat L :=
  fun j i => ∑ S : Finset (Fin B.T),
    if S.card = r ∧ (pathWord B S).head? = some i ∧ (pathWord B S).getLast? = some j
    then pathAmplitude B S else 0

def principalFrobenius {L : ℕ} (C : Mat L) (S : Finset (Fin L)) : ℝ :=
  Real.sqrt (∑ i ∈ S, ∑ j ∈ S, ‖C i j‖^2)

def degreeOne {L : ℕ} (B : LCUCircuit L) (j : Fin L) : ℂ :=
  ∑ t : Fin B.T, if B.query t = j then historyX B t * historyY B t else 0

def beta {L : ℕ} (B : LCUCircuit L) (j : Fin L) : ℝ :=
  ∑ t : Fin B.T, if B.query t = j then ‖historyX B t‖^2 else 0

def gamma {L : ℕ} (B : LCUCircuit L) (j : Fin L) : ℝ :=
  ∑ t : Fin B.T, if B.query t = j then ‖historyY B t‖^2 else 0

def sWeight {L : ℕ} (B : LCUCircuit L) (j : Fin L) : ℝ :=
  Real.sqrt (beta B j * gamma B j)

def IsometryMatrix {n m : ℕ} (U : Matrix (Fin n) (Fin m) ℂ) : Prop :=
  U.conjTranspose * U = 1

end
end HamSimTradeoff.AncillaDepth.Supplement


