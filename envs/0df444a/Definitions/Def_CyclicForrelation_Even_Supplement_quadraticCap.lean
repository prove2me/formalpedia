-- Prove2me | Definitions.Def_CyclicForrelation_Even_Supplement_quadraticCap
-- name    : CyclicForrelation_Even_Supplement_quadraticCap
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:47:19.721207+00:00
-- url     : https://prove2.me/theorems/ab904acb-1c28-4787-968e-7007a45d60ad
-- title:
--   Quadratic cap, its diagonal weights, and the odd-cycle lift
-- statement:
--   Let $G=\mathbb F_2^n$ and $N=2^n$. With coordinates indexed by $\{0,\ldots,n-1\}$, define the **quadratic sign** and correction vector by
--   $$Q(x)=(-1)^{\sum_{i<j}x_ix_j},\qquad \eta=\begin{cases}1^n&n\equiv1\pmod4,\\0&\text{otherwise}.\end{cases}$$
--   The sum in the exponent is in $\mathbb F_2$. Using the published normalized Hadamard matrix $H$ and diagonal sign matrix $D_f$, define the **cap constant** and weights as the concrete real matrix expressions
--   $$c_n=\frac1N\operatorname{Tr}(D_Q H D_Q H D_{Q\chi_\eta}H),\qquad w_y=(D_Q H D_{Q\chi_\eta}H D_Q H)_{yy}.$$
--   For a tuple $g=(g_1,\ldots,g_k)$ with $k\ge2$, the **odd lift** is
--   $$\operatorname{lift}(g)=(Qg_1,g_2,\ldots,g_{k-1},Qg_k,Q\chi_\eta).$$
--   The lifted planted tuple applies this operation to the published `plantedTuple`, retaining its arbitrary final sign function $B$.
--
--   These are shared source objects for the odd nonadaptive bound and the odd adaptive reduction. The trace identity, bounds on $w_y$ and $c_n$, and query simulation properties remain proof obligations; none is a defining assumption.
--
--   **Formalization Note** Sign products use Boolean XOR. All matrices are real on the published cube, and traces have normalization $1/N$. The definitions include dimension zero, where direct evaluation gives $c_0=1$; no printed positive-dimensional evaluation of $c_n$ is used as a definition. The total lift is also defined at $k<2$, outside its source uses.
-- source:
--   Yuxin Zhang, Changpeng Shao, STOC 2027 submission #333 (October 2026), pp. 13–16, §2.2, definitions before Lemma 7 and Eqs. (22)–(23); p. 22, odd-cycle reduction

import Definitions.Def_CyclicForrelation_Even_multiShift

namespace CyclicForrelation.Even.Supplement

/-- The exponent of the source's quadratic sign Q, computed in F₂. -/
def quadraticExponent {n : ℕ} (x : Cube n) : ZMod 2 :=
  ∑ i : Fin n, ∑ j : Fin n, if i < j then x i * x j else 0

/-- Boolean encoding of Q(x) = (-1)^(sum_{i<j} x_i x_j). -/
def quadraticBit {n : ℕ} (x : Cube n) : Bool := decide (quadraticExponent x = 1)

/-- The all-ones vector occurs precisely when n ≡ 1 (mod 4). -/
def capEta (n : ℕ) : Cube n := if n % 4 = 1 then fun _ => 1 else 0

def capLast (n : ℕ) (x : Cube n) : Bool :=
  Bool.xor (quadraticBit x) (characterBit (capEta n) x)

/-- The known normalized three-Hadamard trace c_n, with c_0 = 1. -/
noncomputable def capConstant (n : ℕ) : ℝ :=
  Matrix.trace (phaseOracle (quadraticBit (n := n)) * hadamard n *
    phaseOracle quadraticBit * hadamard n * phaseOracle (capLast n) * hadamard n) /
    (cubeSize n : ℝ)

/-- Diagonal weights from Eq. (22); their bounds are not built into the definition. -/
noncomputable def capWeight (n : ℕ) (y : Cube n) : ℝ :=
  let M : Matrix (Cube n) (Cube n) ℝ :=
    phaseOracle (quadraticBit (n := n)) * hadamard n * phaseOracle (capLast n) *
      hadamard n * phaseOracle quadraticBit * hadamard n
  M y y

/-- Multiply the first and last original signs by Q and append the known Qχ_η.
For the source uses k = 2m ≥ 4 (or k = 4), the first and last indices are distinct. -/
def oddLift {n k : ℕ} (g : OracleTuple n k) : OracleTuple n (k + 1) :=
  fun j x => if h : j.val < k then
    if j.val = 0 ∨ j.val + 1 = k then Bool.xor (quadraticBit x) (g ⟨j.val, h⟩ x)
    else g ⟨j.val, h⟩ x
  else capLast n x

/-- The exact odd lift of the published planted tuple, with arbitrary sign function B. -/
def oddPlantedTuple {n m : ℕ} (t : Fin (m - 1) → Cube n)
    (A : Fin (m - 1) → Cube n → Bool) (B : Cube n → Bool) :
    OracleTuple n (2 * m + 1) :=
  oddLift (plantedTuple t A B)

end CyclicForrelation.Even.Supplement


