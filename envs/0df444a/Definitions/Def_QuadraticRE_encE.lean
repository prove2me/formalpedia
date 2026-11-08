-- Prove2me | Definitions.Def_QuadraticRE_encE
-- name    : QuadraticRE_encE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:07:21.281626+00:00
-- url     : https://prove2.me/theorems/4f22a387-d25a-415a-b115-f16a2043a1ef
-- title:
--   The encoding $E_{j,h}$, its decoder and simulator (Construction 4.1)
-- statement:
--   Fix integers $j\ge0$, $h\ge3$, and $L=4^j$, $m=(L-1)/3$. The random tape is $R=(\theta_A,\theta_C,\bar d,N_1,\dots,N_L)$ with $\theta_A\in\mathbb F_2^m$, $\theta_C\in\mathbb F_2^{2m}$, $\bar d\in\mathbb F_2^{L-1}$, $N_i\in\mathbb F_2^{h\times3}$, a string of $\rho=2(L-1)+3hL$ bits. On input $(a,b,c,d)\in\mathbb F_2^4$ the encoder sets $(a_i)=\mathrm{Sh}^j_A(a;\theta_A)$, $(c_i)=\mathrm{Sh}^j_C(c;\theta_C)$, $d_i=\bar d_i$ for $i<L$ and $d_L=d+\sum_{\ell<L}\bar d_\ell$, and outputs
--   $$E_{j,h}(a,b,c,d;R)=(Q_1,\dots,Q_L),\qquad Q_i=N_i\begin{pmatrix}1&0&c_i\\a_i&1&0\\0&b&d_i\end{pmatrix}.$$
--   The same $b$ is used at every leaf. The leaf bits are $y_i=a_ibc_i+d_i$. The decoder is $\mathrm{Dec}_{j,h}(Q_1,\dots,Q_L)=\sum_i\mathbf 1\{\operatorname{rank}Q_i=3\}$ in $\mathbb F_2$, and the simulator is $\mathrm{Sim}_{j,h}(y)=E_{j,h}(0,0,0,y;R')$ on a fresh tape. The $3hL$ output bits are listed in leaf, row, column order.
--
--   This is the degree-two encoding of $abc+d$ that the paper analyses.
--
--   **Formalization Note** The tape is a flat bit vector, read in the order above; the verification file checks that every read is in range and that the blocks fill the tape. At $j=0$ the masks and $\bar d$ are empty and $(a_1,c_1,d_1)=(a,c,d)$. A description *expands* $E_{j,h}$ when, in the variables $x_0,\dots,x_3=(a,b,c,d)$ and the tape bits, it evaluates to every entry of every $Q_i$.
-- source:
--   Orsini, Patra, From Degree Three to Degree Two: Statistical Randomized Encodings for All Functions, STOC 2027 submission manuscript (sha256 0c94deae…), Construction 4.1, pp.16–17; Sim in the proof of Proposition 4.4, p.20

import Mathlib
import Definitions.Def_QuadraticRE_Sh
import Definitions.Def_QuadraticRE_Desc

namespace QuadraticRE

/-- The matrix `M(a, b, c, d)` of Construction 4.1, Orsini, Patra, *From Degree Three to Degree Two*, STOC 2027 submission manuscript (sha256 0c94deae…), p.17. -/
def matM (a b c d : F2) : Matrix (Fin 3) (Fin 3) F2 :=
  !![1, 0, c; a, 1, 0; 0, b, d]

/-- The tape length `ρ = 2(L − 1) + 3hL`, p.17. -/
def rho (j h : ℕ) : ℕ := 2 * (4 ^ j - 1) + 3 * h * 4 ^ j

/-- The output length `3hL`, p.17. -/
def outLen (j h : ℕ) : ℕ := 3 * h * 4 ^ j

/-- The random tape `R = (θ_A, θ_C, d̄, N₁, …, N_L)`, flat, in this order (`m + 2m + (L − 1) + 3hL`
bits; `3m = L − 1`). -/
abbrev Tape (j h : ℕ) : Type := Fin (rho j h) → F2

/-- An output `(Q₁, …, Q_L)`: `L` binary `h × 3` matrices. -/
abbrev Encoded (j h : ℕ) : Type := Fin (4 ^ j) → Matrix (Fin h) (Fin 3) F2

variable {j h : ℕ}

/-- The block `θ_A` of the tape. -/
def thetaA (R : Tape j h) : Fin (mA j) → F2 := fun t => rd R t

/-- The block `θ_C` of the tape. -/
def thetaC (R : Tape j h) : Fin (2 * mA j) → F2 := fun t => rd R (mA j + t)

/-- The block `d̄` of the tape. -/
def dbar (R : Tape j h) : Fin (4 ^ j - 1) → F2 := fun t => rd R (3 * mA j + t)

/-- The coefficient matrix `N_i` of the tape, in leaf, row, column order. -/
def Nmat (R : Tape j h) (i : Fin (4 ^ j)) : Matrix (Fin h) (Fin 3) F2 :=
  Matrix.of fun r c => rd R (2 * (4 ^ j - 1) + i.val * (3 * h) + r.val * 3 + c.val)

/-- The additive sharing of `d`, p.17: `d_i = d̄_i` for `i < L`, `d_L = d + ∑_{ℓ<L} d̄_ℓ`. -/
def dShare (d : F2) (R : Tape j h) (i : Fin (4 ^ j)) : F2 :=
  if hi : i.val < 4 ^ j - 1 then dbar R ⟨i.val, hi⟩ else d + ∑ t, dbar R t

/-- The leaf shares `a_i`. -/
def leafA (a : F2) (R : Tape j h) : Fin (4 ^ j) → F2 := Sh .A j a (thetaA R)

/-- The leaf shares `c_i`. -/
def leafC (c : F2) (R : Tape j h) : Fin (4 ^ j) → F2 := Sh .C j c (thetaC R)

/-- The leaf bits `y_i = a_i b c_i + d_i`, p.16. The same `b` is used at every leaf. -/
def leafY (a b c d : F2) (R : Tape j h) (i : Fin (4 ^ j)) : F2 :=
  leafA a R i * b * leafC c R i + dShare d R i

/-- The encoder `E_{j,h}(a, b, c, d; R) = (Q₁, …, Q_L)`, `Q_i = N_i M(a_i, b, c_i, d_i)`, Construction
4.1, pp.16–17. -/
def encE (j h : ℕ) (a b c d : F2) (R : Tape j h) : Encoded j h :=
  fun i => Nmat R i * matM (leafA a R i) b (leafC c R i) (dShare d R i)

/-- The decoder `Dec_{j,h}(Q₁, …, Q_L) = ∑_i 1{rank Q_i = 3}` in `F₂`, p.17. -/
noncomputable def decE (j h : ℕ) (Q : Encoded j h) : F2 :=
  ∑ i, if (Q i).rank = 3 then 1 else 0

/-- The simulator `Sim_{j,h}(y) = E_{j,h}(0, 0, 0, y; R′)` on a fresh tape, proof of Prop 4.4, p.20. -/
def simE (j h : ℕ) (y : F2) (R : Tape j h) : Encoded j h :=
  encE j h 0 0 0 y R

/-- The position of an output bit in the string of `3hL` bits, "listing their entries in leaf, row,
and column order", p.17. -/
def flatIdx (i : Fin (4 ^ j)) (r : Fin h) (c : Fin 3) : Fin (outLen j h) :=
  ⟨i.val * (3 * h) + r.val * 3 + c.val, by
    have hi := i.isLt
    have hr := r.isLt
    have hc := c.isLt
    have h1 : (i.val + 1) * (3 * h) ≤ 4 ^ j * (3 * h) := Nat.mul_le_mul_right _ hi
    unfold outLen
    nlinarith⟩

/-- A description `D` expands `E_{j,h}`, in the variables `(a, b, c, d)` = `x 0, x 1, x 2, x 3` and the
tape: every entry of every `Q_i` is the corresponding coordinate of `D`. -/
def Expands (D : Desc 4 (rho j h) (outLen j h)) : Prop :=
  ∀ (x : Fin 4 → F2) (R : Tape j h) (i : Fin (4 ^ j)) (r : Fin h) (c : Fin 3),
    D.eval x R (flatIdx i r c) = encE j h (x 0) (x 1) (x 2) (x 3) R i r c

end QuadraticRE


