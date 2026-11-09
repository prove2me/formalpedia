-- Prove2me | Definitions.Def_LeeYangGap_SpectralGap_Trotter
-- name    : LeeYangGap_SpectralGap_Trotter
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:10:57.091613+00:00
-- url     : https://prove2.me/theorems/798d5ba1-1ac4-4795-a318-2b568ef444b2
-- title:
--   Cyclic Trotter partition polynomial, insertions and moments
-- statement:
--   Let $B$ be an ordered bond list, $M\ge1$ an integer and $\epsilon=\beta/M$. The ordered half-step is $L=\prod_{ij}e^{-\epsilon H_{ij}/2}$. For independent complex variables $y_{i,m}$ at every site and cyclic layer $m\in\mathbb Z_M$, let $D_m(y)$ have diagonal entries $\prod_i y_{i,m}^{x_i}$. Define
--   $$\mathcal Z_\epsilon(y)=\operatorname{Tr}\prod_{m=0}^{M-1}LD_m(y)L^\dagger.$$
--   The companion multivariate polynomial is the cyclic configuration expansion with coefficient factors $(L^\dagger L)_{x_m,x_{m+1}}$ and $x_M=x_0$; all intermediate-layer variables are retained. Define $S_\epsilon=Le^{\epsilon h\sum_iZ_i}L^\dagger$, $S_\epsilon^{(S)}=Le^{\epsilon h\sum_iZ_i}Z_SL^\dagger$ and
--   $$f_{S,\epsilon}(k)=\frac{\operatorname{Tr}(S_\epsilon^{(S)}S_\epsilon^{k-1}S_\epsilon^{(S)}S_\epsilon^{M-k-1})}{\operatorname{Tr}S_\epsilon^M}-\left(\frac{\operatorname{Tr}(S_\epsilon^{(S)}S_\epsilon^{M-1})}{\operatorname{Tr}S_\epsilon^M}\right)^2.$$
--   For $\widetilde Z_S=LZ_SL^{-1}$ the moment definitions are $G_{1,\epsilon}=\operatorname{Tr}(\widetilde Z_SS_\epsilon^M)/\operatorname{Tr}S_\epsilon^M$ and $G_{2,\epsilon}(k)=\operatorname{Tr}(\widetilde Z_SS_\epsilon^k\widetilde Z_SS_\epsilon^{M-k})/\operatorname{Tr}S_\epsilon^M$. The point $y_\star$ has every coordinate $e^{-2\epsilon h}$, and $\sigma_m$ changes precisely the signs at $S\times\{m\}$. The layer distance is $d_k=\min(k,M-k)+1$. Interior-layer theorems guard $1\le k<M$; the denominators are positive traces of positive-definite powers. These constructions are shared by all discrete and comparison milestones.
-- source:
--   Chaithanya Rayudu, Jun Takahashi, Spectral gap of Lee-Yang Hamiltonians, STOC 2027 submission #575 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/575.pdf, pp. 5–8, Eqs. (3)–(5), (12)–(19); p. 20, Eqs. (78)–(79)

import Mathlib
import Definitions.Def_LeeYangGap_SpectralGap_Model
open scoped BigOperators Matrix Matrix.Norms.L2Operator
set_option autoImplicit false
noncomputable section

namespace LeeYangGap.SpectralGap
abbrev Location (n M : ℕ) := Fin n × Fin M
abbrev LayerVariables (n M : ℕ) := Location n M → ℂ

def stepSize (β : ℝ) (M : ℕ) : ℝ := β / M

def layerL {n : ℕ} (B : System n) (ε : ℝ) : QOp n :=
  (B.map (fun b => mexp ((-ε / 2 : ℂ) • bondHamiltonian b))).prod

def layerD {n M : ℕ} (y : LayerVariables n M) (m : Fin M) : QOp n :=
  Matrix.diagonal (fun x => ∏ i : Fin n, y (i,m) ^ (x i).val)

def trotterPartition {n : ℕ} (B : System n) (β : ℝ) (M : ℕ)
    (y : LayerVariables n M) : ℂ :=
  let L := layerL B (stepSize β M)
  Matrix.trace ((List.ofFn (fun m : Fin M => L * layerD y m * Lᴴ)).prod)

/-- Modular successor; the empty layer type has no input. -/
def nextLayer {M : ℕ} (m : Fin M) : Fin M :=
  ⟨(m.val + 1) % M, Nat.mod_lt _ (Nat.zero_lt_of_lt m.isLt)⟩

/-- Eq. (4), as an actual multivariate polynomial with all layer variables. -/
def partitionPolynomial {n : ℕ} (B : System n) (β : ℝ) (M : ℕ) :
    MvPolynomial (Location n M) ℂ :=
  let L := layerL B (stepSize β M)
  ∑ x : Fin M → Config n,
    ∏ m : Fin M,
      MvPolynomial.C ((Lᴴ * L) (x m) (x (nextLayer m))) *
        ∏ i : Fin n, (MvPolynomial.X (i,m)) ^ (x m i).val

def trotterStep {n : ℕ} (B : System n) (h ε : ℝ) : QOp n :=
  let L := layerL B ε
  L * mexp ((ε * h : ℂ) • fieldSum n) * Lᴴ

def insertedStep {n : ℕ} (B : System n) (h ε : ℝ) (S : Finset (Fin n)) : QOp n :=
  let L := layerL B ε
  L * mexp ((ε * h : ℂ) • fieldSum n) * zProduct S * Lᴴ

def trotterConnected {n : ℕ} (B : System n) (h β : ℝ) (M : ℕ)
    (S : Finset (Fin n)) (k : ℕ) : ℂ :=
  let R := trotterStep B h (stepSize β M)
  let I := insertedStep B h (stepSize β M) S
  Matrix.trace (I * R^(k-1) * I * R^(M-k-1)) / Matrix.trace (R^M) -
    (Matrix.trace (I * R^(M-1)) / Matrix.trace (R^M))^2

def conjugatedZ {n : ℕ} (B : System n) (ε : ℝ) (S : Finset (Fin n)) : QOp n :=
  layerL B ε * zProduct S * (layerL B ε)⁻¹

def trotterMomentOne {n : ℕ} (B : System n) (h β : ℝ) (M : ℕ)
    (S : Finset (Fin n)) : ℂ :=
  let R := trotterStep B h (stepSize β M)
  Matrix.trace (conjugatedZ B (stepSize β M) S * R^M) / Matrix.trace (R^M)

def trotterMomentTwo {n : ℕ} (B : System n) (h β : ℝ) (M : ℕ)
    (S : Finset (Fin n)) (k : ℕ) : ℂ :=
  let R := trotterStep B h (stepSize β M)
  let I := conjugatedZ B (stepSize β M) S
  Matrix.trace (I * R^k * I * R^(M-k)) / Matrix.trace (R^M)

def starPoint {n M : ℕ} (h β : ℝ) : LayerVariables n M :=
  fun _ => (Real.exp (-2 * stepSize β M * h) : ℂ)

def reflectLayer {n M : ℕ} (S : Finset (Fin n)) (m : ℕ)
    (y : LayerVariables n M) : LayerVariables n M :=
  fun l => if l.1 ∈ S ∧ l.2.val = m then -y l else y l

def layerDistance (M k : ℕ) : ℕ := min k (M-k) + 1
end LeeYangGap.SpectralGap


