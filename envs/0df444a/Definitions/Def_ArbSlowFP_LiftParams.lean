-- Prove2me | Definitions.Def_ArbSlowFP_LiftParams
-- name    : ArbSlowFP_LiftParams
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:52:34.722205+00:00
-- url     : https://prove2.me/theorems/c2bf74fa-dbf7-4a69-80f2-87a98f055031
-- title:
--   The lift: tables (46)–(55), (59), words, priority (63) and the next clock
-- statement:
--   Fix an order-$k$ parent with additional data $(\tau,c_{\mathrm{ref}},\ell_*,a_P)$ and a rational linear map $\mathcal R$ with $L(\mathcal R(F))=F$ on the image of $L$. Write $r=w=k+1$, $H=A_k+3$, and let $\lambda$ be the least positive integer with $\lambda\zeta^\circ$ integral. For integers $T_1,T_2$ the **lift** is:
--   $$\upsilon=T_1\lambda\zeta^\circ,\quad \ell=2r\lambda T_1\zeta^\circ+\ell_*,\quad E_0=2r\lambda(\zeta^\circ)^\top\zeta^\circ,$$
--   the gain $c=c_{\mathrm{ref}}-\langle Z^{(k)},(D^\circ)^\top X-\ell_*^\top\psi^\circ\rangle/((\mathbf 1^\top X)_k+\ell_k)$ for even $k$ and $c=c_{\mathrm{ref}}$ for odd $k$, $\delta=\tfrac12\min\{\delta_0,c\}$,
--   $$E=T_1E_0+\mathcal R(D^\top X-\ell^\top\psi-T_1L(E_0)),\quad W=\mathbf 1_r\upsilon+T_2V_0,\quad W_E=W+e_0\ell_*,\quad M=\begin{pmatrix}W_E\\W\end{pmatrix},$$
--   the closed-form inverses $W^{-1}=T_1^{-1}\Phi_0+T_2^{-1}\Phi_1$ and $W_E^{-1}$ of (53), the interaction matrix $J=\begin{pmatrix}\eta L_r&0\\C_\times&\eta L_r\end{pmatrix}$ of (54), the coupling $P$ from (39) with $P_0=[-a\mathbf 1_r^\top\,|\,a\mathbf 1_r^\top]$, $R_M=[0\,|\,W^{-1}]$, $L_X=X(X^\top X)^{-1}$, and the payoff matrix $G$ of (35).
--
--   The **rotated tables** are $R_+=\mathrm{col}(S_{\mathrm{mid}},\mathbf 1_{2r}\zeta-JM)$ and $C_+=\mathrm{col}(XT,M)$, with words $A(q)=W_k(\tau q)\cdots W_k(2\tau q-1)\,g$, $B(q)=a_0^{m_0(q)}\cdots a_{2r-1}^{m_{2r-1}(q)}$, $W_{k+1}(q)=B(q)A(q+1)$, and the priority
--   $$\text{parent actions}\prec a_{2r-1}\prec a_{2r-2}\prec\dots\prec a_0\prec g .$$
--
--   The module also gives `IsAdmissible` ($T_2\ge\max\{T_1,\upsilon_k\}$), `ResetBoundsAt` (the exact output and sign properties of Lemma 7.5), `IsOuterThreshold` (the conclusion of Proposition 7.7), `nextClock`, and the action types `FamAct` of the recursive family.
--
--   **Formalization Note** The actions are `(ι ⊕ Unit) ⊕ (Fin (k+1) ⊕ Fin (k+1))`: old actions, then the early and the late reset group. $W^{-1}$ and $W_E^{-1}$ are the printed closed forms, so no junk inverse arises for them. Run lengths take the floor and `toNat` of $m_j(q)$, and Proposition 7.7 asserts that $m_j(q)$ is exactly this natural number. $\mathcal R$ is any linear section on all matrices. The division in the gain has a nonzero denominator for $T_1\ge T_0$ (Proposition 7.4); statements only use it there.
-- source:
--   Abernethy, Lazarsfeld, Wibisono, Arbitrarily Slow Polynomial Convergence of Fictitious Play, arXiv:2610.08768 (version of November 3, 2026, sha256 977c34b6…), pp.40, 49–52, 55, 57–58, 61; eqs. (35), (46)–(48), (51)–(55), (59), (63)

import Mathlib
import Definitions.Def_ArbSlowFP_ValidFrom
import Definitions.Def_ArbSlowFP_IsAddData

open Matrix

namespace ArbSlowFP

/-- The actions of the lifted game (§6.4, p.40): old actions `ι ⊕ Unit` (parent actions and the
endpoint action `g`), then the early and the late reset group, each of `r = k + 1` actions. -/
abbrev LiftAct (k : ℕ) (ι : Type*) := (ι ⊕ Unit) ⊕ (Fin (k + 1) ⊕ Fin (k + 1))

/-- The endpoint action `g` of (28). -/
def actG {k : ℕ} {ι : Type*} : LiftAct k ι := Sum.inl (Sum.inr ())

/-- The first reset action `a₀`. -/
def actA0 {k : ℕ} {ι : Type*} : LiftAct k ι := Sum.inr (Sum.inl 0)

instance {k : ℕ} {ι : Type*} : Nonempty (LiftAct k ι) := ⟨actG⟩

/-- A rational linear map `R` with `L(R(F)) = F` for `F ∈ im(L)`, as fixed on p.49 before (48).

**Formalization Note.** The map is any such `ℚ`-linear map on all `w × w` matrices. Every linear
section on `im(L)` extends to such a map, so this covers every choice. -/
def IsSection {w : ℕ} (Rmap : Matrix (Fin w) (Fin w) ℚ →ₗ[ℚ] Matrix (Fin w) (Fin w) ℚ) : Prop :=
  ∀ F, (∃ E, opL E = F) → opL (Rmap F) = F

/-- The fixed parent data of §7.2, p.48: the bare tables, `A_k`, `δ₀`, the additional data
`(τ, cref, ℓ∗, a_P)` of Definition 6.2, and the linear map `R` of p.49. -/
structure LiftParams (k : ℕ) (ι : Type*) where
  /-- The bare parent tables. -/
  P : Parent k ι
  /-- The parent's remaining-height constant. -/
  Ak : ℚ
  /-- The parent's prefix margin. -/
  δ0 : ℚ
  /-- The scale. -/
  τ : ℕ
  /-- The reference gain. -/
  cref : ℚ
  /-- The integer correction row. -/
  ℓs : Fin (k + 1) → ℚ
  /-- The positive parent weights. -/
  aP : ι → ℚ
  /-- The linear section of `L`. -/
  Rmap : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ →ₗ[ℚ] Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ

namespace LiftParams

variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (L : LiftParams k ι)

/-- The baseline `H = A_k + 3`, p.36. -/
def H : ℚ := L.Ak + 3

/-- The reference height row `ζ°`, p.37. -/
def zo : Fin (k + 1) → ℚ := L.P.zeta L.H L.τ L.cref

/-- The least positive integer `λ` for which `λζ°` has integer entries, p.49. -/
def lam : ℕ := Finset.univ.lcm fun j => (L.zo j).den

/-- `υ = T₁λζ°` of (46). -/
def upsilon (T1 : ℕ) : Fin (k + 1) → ℚ := ((T1 : ℚ) * (L.lam : ℚ)) • L.zo

/-- `ℓ = T₁ℓ₀ + ℓ∗`, `ℓ₀ = 2rλζ°` of (46), `r = k + 1`. -/
def ell (T1 : ℕ) : Fin (k + 1) → ℚ :=
  ((T1 : ℚ) * (2 * ((k : ℚ) + 1) * (L.lam : ℚ))) • L.zo + L.ℓs

/-- `E₀ = 2rλ(ζ°)⊤ζ°` of (46). -/
def E0 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ :=
  (2 * ((k : ℚ) + 1) * (L.lam : ℚ)) • Matrix.vecMulVec L.zo L.zo

/-- The actual gain `c`: (47) for even `k`, and `c = cref` for odd `k`, p.49. -/
def gain (T1 : ℕ) : ℚ :=
  if Even k then
    L.cref - frob (testZ k k) (L.P.testResidual L.H L.τ L.cref L.ℓs) /
      ((1 ᵥ* L.P.X L.τ) (Fin.last k) + L.ell T1 (Fin.last k))
  else L.cref

/-- `δ = ½ min{δ₀, c}`, p.49. -/
def delta (T1 : ℕ) : ℚ := (1 / 2) * min L.δ0 (L.gain T1)

/-- The actual height row `ζ`, by (27) at gain `c`. -/
def zeta (T1 : ℕ) : Fin (k + 1) → ℚ := L.P.zeta L.H L.τ (L.gain T1)

/-- The row `ψ = ζB - ζ` at gain `c`. -/
def psi (T1 : ℕ) : Fin (k + 1) → ℚ := L.P.psi L.H L.τ (L.gain T1)

/-- The actual table `S` of (28), with gain `c` and margin `δ`. -/
def S (T1 : ℕ) : Matrix (ι ⊕ Unit) (Fin (k + 1)) ℚ := L.P.S L.H L.τ (L.gain T1) (L.delta T1)

/-- The actual table `S_mid` of (28). -/
def Smid (T1 : ℕ) : Matrix (ι ⊕ Unit) (Fin (k + 1)) ℚ :=
  L.P.Smid L.H L.τ (L.gain T1) (L.delta T1)

/-- The actual table `D` of (28). -/
def D (T1 : ℕ) : Matrix (ι ⊕ Unit) (Fin (k + 1)) ℚ := L.P.D L.H L.τ (L.gain T1) (L.delta T1)

/-- The argument `D⊤X - ℓ⊤ψ - T₁L(E₀)` of `R` in (48). -/
def Earg (T1 : ℕ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ :=
  (L.D T1)ᵀ * L.P.X L.τ - Matrix.vecMulVec (L.ell T1) (L.psi T1) - (T1 : ℚ) • opL L.E0

/-- The aggregate interaction matrix `E = T₁E₀ + R(D⊤X - ℓ⊤ψ - T₁L(E₀))` of (48). -/
def E (T1 : ℕ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ :=
  (T1 : ℚ) • L.E0 + L.Rmap (L.Earg T1)

/-- The adjustment matrix `V₀ = [[I_k, 0], [-1⊤_k, 0]]` of (51). -/
def V0 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ :=
  Matrix.of fun i j =>
    if (j : ℕ) = k then 0
    else if (i : ℕ) = k then -1
    else if (i : ℕ) = (j : ℕ) then 1 else 0

/-- The late count table `W = 1_r υ + T₂V₀` of (51). -/
def W (T1 T2 : ℕ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ :=
  (Matrix.of fun _ j => L.upsilon T1 j) + (T2 : ℚ) • (V0 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)

/-- The early count table `W_E = W + e₀ℓ∗` of (51). -/
def WE (T1 T2 : ℕ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ :=
  L.W T1 T2 + (Matrix.of fun (i j : Fin (k + 1)) => if (i : ℕ) = 0 then L.ℓs j else 0)

/-- The reset count table `M = col(W_E, W)` of (51). -/
def M (T1 T2 : ℕ) : Matrix (Fin (k + 1) ⊕ Fin (k + 1)) (Fin (k + 1)) ℚ :=
  Matrix.fromRows (L.WE T1 T2) (L.W T1 T2)

/-- `Φ₀ = e_k 1⊤_r / (rλζ°_k)` of (52). -/
def Phi0 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ :=
  Matrix.of fun i _ =>
    if (i : ℕ) = k then 1 / (((k : ℚ) + 1) * (L.lam : ℚ) * L.zo (Fin.last k)) else 0

/-- `Φ₁ = col(I_k, -ζ°_{0:(k-1)}/ζ°_k) Π`, `Π = [I_k | 0_k] - r⁻¹1_k1⊤_r`, of (52). -/
def Phi1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ :=
  Matrix.of fun i j =>
    ∑ l : Fin k,
      (if (i : ℕ) = k then -L.zo l.castSucc / L.zo (Fin.last k)
        else if (i : ℕ) = (l : ℕ) then 1 else 0) *
      ((if (l : ℕ) = (j : ℕ) then 1 else 0) - 1 / ((k : ℚ) + 1))

/-- `W⁻¹ = T₁⁻¹Φ₀ + T₂⁻¹Φ₁`, the closed form in (53). -/
def Winv (T1 T2 : ℕ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ :=
  (T1 : ℚ)⁻¹ • L.Phi0 + (T2 : ℚ)⁻¹ • L.Phi1

/-- `W_E⁻¹ = W⁻¹ - W⁻¹e₀ℓ∗W⁻¹/(1 + ℓ∗W⁻¹e₀)`, the closed form in (53). -/
def WEinv (T1 T2 : ℕ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ :=
  L.Winv T1 T2 -
    (1 + L.ℓs ⬝ᵥ (fun i => L.Winv T1 T2 i 0))⁻¹ •
      Matrix.vecMulVec (fun i => L.Winv T1 T2 i 0) (L.ℓs ᵥ* L.Winv T1 T2)

/-- `L_r`: ones strictly below the diagonal, p.51. -/
def Lr : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ :=
  Matrix.of fun i j => if (j : ℕ) < (i : ℕ) then 1 else 0

/-- `η = 1/(T₁T₂²)` of (54). -/
def eta (T1 T2 : ℕ) : ℚ := 1 / ((T1 : ℚ) * (T2 : ℚ) ^ 2)

/-- `κ = 2/(rλT₁)` of (54). -/
def kappa (T1 : ℕ) : ℚ := 2 / (((k : ℚ) + 1) * (L.lam : ℚ) * (T1 : ℚ))

/-- `E_base = T₁E₀ + 2(ζ°)⊤ℓ∗` of (54). -/
def Ebase (T1 : ℕ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ :=
  (T1 : ℚ) • L.E0 + (2 : ℚ) • Matrix.vecMulVec L.zo L.ℓs

/-- `F_res = E - E_base - η(W_E⊤L_rW_E + W⊤L_rW)` of (54). -/
def Fres (T1 T2 : ℕ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ :=
  L.E T1 - L.Ebase T1 -
    eta T1 T2 • ((L.WE T1 T2)ᵀ * Lr * L.WE T1 T2 + (L.W T1 T2)ᵀ * Lr * L.W T1 T2)

/-- `C× = κ1_r1⊤_r + W⁻⊤F_resW_E⁻¹` of (54). -/
def Cx (T1 T2 : ℕ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ :=
  (Matrix.of fun _ _ => L.kappa T1) + (L.Winv T1 T2)ᵀ * L.Fres T1 T2 * L.WEinv T1 T2

/-- `J = [[ηL_r, 0], [C×, ηL_r]]` of (54). -/
def J (T1 T2 : ℕ) : Matrix (Fin (k + 1) ⊕ Fin (k + 1)) (Fin (k + 1) ⊕ Fin (k + 1)) ℚ :=
  Matrix.fromBlocks (eta T1 T2 • Lr) 0 (L.Cx T1 T2) (eta T1 T2 • Lr)

/-- The weight vector `a = col(a_P, 2H - cref)` of (32). -/
def a : ι ⊕ Unit → ℚ := Sum.elim L.aP fun _ => 2 * L.H - L.cref

/-- `a_min = min_{0≤i≤g} a_i` of Lemma 7.5 (iv), p.53. -/
def aMin : ℚ := Finset.univ.inf' Finset.univ_nonempty L.a

/-- The reference coupling `P₀ = [-a1⊤_r | a1⊤_r]` of (55). -/
def P0 : Matrix (ι ⊕ Unit) (Fin (k + 1) ⊕ Fin (k + 1)) ℚ :=
  Matrix.of fun i j => Sum.elim (fun _ => -L.a i) (fun _ => L.a i) j

/-- `R_M = [0 | W⁻¹]` of (55). -/
def RM (T1 T2 : ℕ) : Matrix (Fin (k + 1)) (Fin (k + 1) ⊕ Fin (k + 1)) ℚ :=
  Matrix.of fun i j => Sum.elim (fun _ => 0) (fun l => L.Winv T1 T2 i l) j

/-- `L_X = X(X⊤X)⁻¹`, p.42. The matrix `X⊤X` is invertible since `X` has full column rank. -/
noncomputable def LX : Matrix (ι ⊕ Unit) (Fin (k + 1)) ℚ :=
  L.P.X L.τ * ((L.P.X L.τ)ᵀ * L.P.X L.τ)⁻¹

/-- The table `Q` of (35) for the lift. -/
def Q (T1 T2 : ℕ) : Matrix (Fin (k + 1) ⊕ Fin (k + 1)) (Fin (k + 1)) ℚ :=
  resetQ (L.zeta T1) (L.J T1 T2) (L.M T1 T2)

/-- The coupling `P` of (39), with the reference matrix and the one-sided inverses of (55). -/
noncomputable def Pc (T1 T2 : ℕ) : Matrix (ι ⊕ Unit) (Fin (k + 1) ⊕ Fin (k + 1)) ℚ :=
  couplingP L.P0 (L.D T1) (L.Q T1 T2) (L.P.X L.τ) (L.M T1 T2) L.LX (L.RM T1 T2)

/-- The lifted payoff matrix `G` of (35). -/
noncomputable def G (T1 T2 : ℕ) : Matrix (LiftAct k ι) (LiftAct k ι) ℚ :=
  liftG L.P.GO (L.Pc T1 T2) (L.J T1 T2)

/-- The full phase-entry score table `U = col(S, V)` of the outer phase `A(q)B(q)`, p.40. -/
def U (T1 T2 : ℕ) : Matrix (LiftAct k ι) (Fin (k + 1)) ℚ :=
  Matrix.fromRows (L.S T1) (resetV (L.zeta T1) (L.J T1 T2) (L.M T1 T2))

/-- The rotated score table `R₊ = col(S_mid, 1_{2r}ζ - JM)` of (59). -/
def Rplus (T1 T2 : ℕ) : Matrix (LiftAct k ι) (Fin (k + 1)) ℚ :=
  Matrix.fromRows (L.Smid T1)
    ((Matrix.of fun _ j => L.zeta T1 j) - L.J T1 T2 * L.M T1 T2)

/-- The rotated count table `C₊ = col(XT, M)` of (59). -/
def Cplus (T1 T2 : ℕ) : Matrix (LiftAct k ι) (Fin (k + 1)) ℚ :=
  Matrix.fromRows (L.P.X L.τ * shiftT (k + 1)) (L.M T1 T2)

/-- The counter row `v₊ = e⊤_g` of Proposition 7.8, p.61. -/
def vPlus : LiftAct k ι → ℚ := fun x => if x = actG then 1 else 0

/-- The bare tables of the next order: `(G, R₊, C₊, a₀, e⊤_g)`. -/
noncomputable def nextParent (T1 T2 : ℕ) : Parent (k + 1) (LiftAct k ι) :=
  ⟨L.G T1 T2, L.Rplus T1 T2, L.Cplus T1 T2, actA0, vPlus⟩

/-- The range `T₂ ≥ max{T₁, υ_k}` of §7.2, with integers `T₁`, `T₂`. -/
def IsAdmissible (T1 T2 : ℕ) : Prop := T1 ≤ T2 ∧ L.upsilon T1 (Fin.last k) ≤ (T2 : ℚ)

/-- The old-block word `A(q) = W_k(τq) ⋯ W_k(2τq-1) g`, p.36, on the old actions. -/
def oldWord (W : ℕ → List ι) (q : ℕ) : List (ι ⊕ Unit) :=
  (bundle W (L.τ * q) (L.τ * q)).map Sum.inl ++ [Sum.inr ()]

/-- The run length of a reset action: the value `m_j(q)` of the count polynomial, as a natural
number. Proposition 7.7 asserts that this value is a nonnegative integer. -/
def runLen (T1 T2 q : ℕ) (j : Fin (k + 1) ⊕ Fin (k + 1)) : ℕ :=
  ⌊(L.M T1 T2 *ᵥ binomBasis (k + 1) (q : ℤ)) j⌋.toNat

/-- The reset word `B(q) = a₀^{m₀(q)} ⋯ a_{2r-1}^{m_{2r-1}(q)}`, p.40. Early actions come first, then
late actions; each group is in increasing order of index. -/
def resetWord (T1 T2 q : ℕ) : List (Fin (k + 1) ⊕ Fin (k + 1)) :=
  (List.finRange (k + 1)).flatMap (fun j => List.replicate (L.runLen T1 T2 q (Sum.inl j)) (Sum.inl j))
    ++ (List.finRange (k + 1)).flatMap
        (fun j => List.replicate (L.runLen T1 T2 q (Sum.inr j)) (Sum.inr j))

/-- The unrotated outer word `A(q)B(q)`, on all actions. -/
def outerWord (W : ℕ → List ι) (T1 T2 q : ℕ) : List (LiftAct k ι) :=
  (L.oldWord W q).map Sum.inl ++ (L.resetWord T1 T2 q).map Sum.inr

/-- The rotated phase word `W_{k+1}(q) = B(q)A(q+1)` of (59). -/
def nextWord (W : ℕ → List ι) (T1 T2 q : ℕ) : List (LiftAct k ι) :=
  (L.resetWord T1 T2 q).map Sum.inr ++ (L.oldWord W (q + 1)).map Sum.inl

/-- The priority (63), p.57: parent actions in their inherited order, then
`a_{2r-1} ≺ a_{2r-2} ≺ ⋯ ≺ a₀ ≺ g`. With `B = sup rank + 1`, a parent action keeps its rank, and the
late action `j` and the early action `j` get `B + (r-1-j)` and `B + r + (r-1-j)`, and `g` gets
`B + 2r`. -/
def liftRank (rank : ι → ℕ) : LiftAct k ι → ℕ
  | Sum.inl (Sum.inl i) => rank i
  | Sum.inl (Sum.inr _) => Finset.univ.sup rank + 1 + 2 * (k + 1)
  | Sum.inr (Sum.inr j) => Finset.univ.sup rank + 1 + (k - (j : ℕ))
  | Sum.inr (Sum.inl j) => Finset.univ.sup rank + 1 + (k + 1) + (k - (j : ℕ))

/-- The conclusion of Proposition 7.7 at a threshold `Qout`, p.58. For every `q ≥ Qout` the reset
counts are nonnegative integers, the word `A(q)B(q)` is followed by the process (6) under the
priority (63) from `u(q)` and ends at `u(q+1)`, and the maximum score over all actions equals `ζ(q)`
throughout the reset block, including its entry and endpoint. -/
def IsOuterThreshold (rank : ι → ℕ) (W : ℕ → List ι) (T1 T2 Qout : ℕ) : Prop :=
  ∀ q, Qout ≤ q →
    (∀ j, ((L.runLen T1 T2 q j : ℕ) : ℚ) = (L.M T1 T2 *ᵥ binomBasis (k + 1) (q : ℤ)) j) ∧
    ValidFrom (L.G T1 T2) (liftRank rank) (L.U T1 T2 *ᵥ binomBasis (k + 1) (q : ℤ))
      (L.outerWord W T1 T2 q) ∧
    scoreAfter (L.G T1 T2) (L.U T1 T2 *ᵥ binomBasis (k + 1) (q : ℤ)) (L.outerWord W T1 T2 q) =
      L.U T1 T2 *ᵥ binomBasis (k + 1) ((q : ℤ) + 1) ∧
    ∀ h, h ≤ (L.resetWord T1 T2 q).length →
      height (scoreAfter (L.G T1 T2) (L.U T1 T2 *ᵥ binomBasis (k + 1) (q : ℤ))
        ((L.oldWord W q).map Sum.inl ++ ((L.resetWord T1 T2 q).take h).map Sum.inr)) =
      L.zeta T1 ⬝ᵥ binomBasis (k + 1) (q : ℤ)

/-- The exact output of §7.2.2, p.52, and the sign and margin properties (i)–(iv) of Lemma 7.5, p.52,
at the parameters `(T₁, T₂)`: `PM = D`, `P⊤X = Q`, `M⊤JM = E`, `L(E) = D⊤X - ℓ⊤ψ`, the inverses in
(53), and `GC₊ = R₊N`; (i) `0 < c < 1` and `γ = M_{:,k} > 0`; (ii) `C× > 0`, `η > 0`; (iii)
`P_E < 0 < P_L`; (iv) the margins (57) with `ϵ = a_min/4`. -/
structure ResetBoundsAt (T1 T2 : ℕ) : Prop where
  PM_eq : L.Pc T1 T2 * L.M T1 T2 = L.D T1
  PX_eq : (L.Pc T1 T2)ᵀ * L.P.X L.τ = L.Q T1 T2
  MJM_eq : (L.M T1 T2)ᵀ * L.J T1 T2 * L.M T1 T2 = L.E T1
  E_compat : opL (L.E T1) = (L.D T1)ᵀ * L.P.X L.τ - Matrix.vecMulVec (L.ell T1) (L.psi T1)
  W_inv : L.W T1 T2 * L.Winv T1 T2 = 1
  WE_inv : L.WE T1 T2 * L.WEinv T1 T2 = 1
  GC_eq : L.G T1 T2 * L.Cplus T1 T2 = L.Rplus T1 T2 * shiftN (k + 1)
  gain_pos : 0 < L.gain T1
  gain_lt : L.gain T1 < 1
  gamma_pos : ∀ j, 0 < L.M T1 T2 j (Fin.last k)
  Cx_pos : ∀ i j, 0 < L.Cx T1 T2 i j
  eta_pos : 0 < eta T1 T2
  early_neg : ∀ i j, L.Pc T1 T2 i (Sum.inl j) < 0
  late_pos : ∀ i j, 0 < L.Pc T1 T2 i (Sum.inr j)
  /-- (57), first margin: `-P_ij > ϵ` for `ϵ = a_min/4`. -/
  wait_parent : ∀ (i : ι) (j : Fin (k + 1)), L.aMin / 4 < -L.Pc T1 T2 (Sum.inl i) (Sum.inl j)
  /-- (57), second margin: `-P_gj - c > A_k`. -/
  wait_endpoint : ∀ j : Fin (k + 1),
    L.Ak < -L.Pc T1 T2 (Sum.inr ()) (Sum.inl j) - L.gain T1

/-- The next-order clock data: `(G, (63), R₊, C₊, a₀, e⊤_g, Q_{k+1}, W_{k+1}, δ₀,₊, A_{k+1}, Q̂_{k+1})`,
with `δ₀,₊ = 1` and `A_{k+1} = A_k + 1` of Proposition 7.8, p.61. -/
noncomputable def nextClock (rank : ι → ℕ) (W : ℕ → List ι) (T1 T2 Qout : ℕ)
    (Qhat : ℕ → ℕ → ℕ) : ClockData (k + 1) (LiftAct k ι) where
  A := L.G T1 T2
  rank := liftRank rank
  R := L.Rplus T1 T2
  C := L.Cplus T1 T2
  b := actA0
  v := vPlus
  Q := Qout
  W := L.nextWord W T1 T2
  δ0 := 1
  Ak := L.Ak + 1
  Qhat := Qhat

end LiftParams

/-- The parent data of `LiftParams` taken from a clock. -/
def ClockData.liftParams {k : ℕ} {ι : Type*} (d : ClockData k ι) (τ : ℕ) (cref : ℚ)
    (ℓs : Fin (k + 1) → ℚ) (aP : ι → ℚ)
    (Rmap : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ →ₗ[ℚ] Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) :
    LiftParams k ι :=
  ⟨d.parent, d.Ak, d.δ0, τ, cref, ℓs, aP, Rmap⟩

/-- The recursive family's action types, indexed by `j` with `k = j + 2`: `Fin 3` at order 2, then
the lifted actions at each step. -/
def FamAct : ℕ → Type
  | 0 => Fin 3
  | j + 1 => LiftAct (j + 2) (FamAct j)

instance famDecEq : ∀ j, DecidableEq (FamAct j)
  | 0 => inferInstanceAs (DecidableEq (Fin 3))
  | j + 1 => by
      have := famDecEq j
      exact inferInstanceAs (DecidableEq (LiftAct (j + 2) (FamAct j)))

instance famFintype : ∀ j, Fintype (FamAct j)
  | 0 => inferInstanceAs (Fintype (Fin 3))
  | j + 1 => by
      have := famFintype j
      exact inferInstanceAs (Fintype (LiftAct (j + 2) (FamAct j)))

instance famNonempty : ∀ j, Nonempty (FamAct j)
  | 0 => inferInstanceAs (Nonempty (Fin 3))
  | j + 1 => inferInstanceAs (Nonempty (LiftAct (j + 2) (FamAct j)))

end ArbSlowFP


