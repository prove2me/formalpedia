-- Prove2me | Definitions.Def_RamareFiniteBounds
-- name    : RamareFiniteBounds
-- status  : Definition
-- author  : @cm_beta
-- created : 2026-09-19T18:45:38.326621+00:00
-- url     : https://prove2.me/theorems/e2a7a44e-4d59-4ca8-b8b1-ce37a6190f48
-- title:
--   Integer majorants and endpoints for the finite Ramaré bound
-- statement:
--   Let $\varphi(n)$ be Euler's totient and put $D=10^{10}$. Define the integer majorant
--
--   $$
--   w_D(n)=\begin{cases}\lfloor D/\varphi(n)\rfloor+1,&n\text{ squarefree},\\0,&\text{otherwise},\end{cases}
--   \qquad W_D(N)=\sum_{n=1}^{N}w_D(n).
--   $$
--
--   The endpoint table consists of 74 explicit records $(a,b,k,U)$. The interval endpoints run from $(1,1)$ to $(139546,142300)$; $k$ is the exponent used for a power-of-two reduction of the logarithm at $a$, and $U$ is the proposed integer prefix value at $b$.
--
--   This bundle defines the arithmetic functions and stores the complete endpoint table. It makes no assertion that the entries are correct. Separate arithmetic and analytic theorems certify the prefix values, interval coverage, and logarithm comparisons. Together these certificates support the finite-range squarefree reciprocal-totient estimate used in Ramaré's inequality.
-- source:
--   Auxiliary integer certificate constructed for the finite verification in O. Ramaré, On Shnirelman's constant, Ann. Scuola Norm. Sup. Pisa 22 (1995), 645–706, Lemma 3.5(1), printed p. 660, equation (3.13). https://www.numdam.org/item/ASNSP_1995_4_22_4_645_0/ . The 74-row table and denominator 10^10 are this formal development's certificate data, not a table transcribed from the paper. Target finite-range statement: https://prove2.me/theorems/d69837d9-f165-45c0-a82c-bdb4d2efa4da .

import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.List.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false
open scoped BigOperators

namespace RamareFiniteBounds

/-- Denominator used by the integer reciprocal majorant. -/
def scale : ℕ := 10000000000

/-- Integer majorant of the squarefree reciprocal-totient summand. -/
def roundedTerm (D n : ℕ) : ℕ :=
  if Squarefree n then D / n.totient + 1 else 0

def roundedPrefix (D N : ℕ) : ℕ :=
  ∑ n ∈ Finset.Icc 1 N, roundedTerm D n

structure LogEndpoint where
  lo : ℕ
  hi : ℕ
  exponent : ℕ
  upper : ℕ
  deriving DecidableEq

def logEndpoints : List LogEndpoint :=
  [
    ⟨1, 1, 0, 10000000001⟩,
    ⟨2, 2, 1, 20000000002⟩,
    ⟨3, 4, 1, 25000000003⟩,
    ⟨5, 5, 2, 27500000004⟩,
    ⟨6, 6, 2, 32500000005⟩,
    ⟨7, 9, 2, 34166666672⟩,
    ⟨10, 12, 3, 37666666674⟩,
    ⟨13, 14, 3, 40166666675⟩,
    ⟨15, 16, 3, 41416666676⟩,
    ⟨17, 20, 4, 42597222233⟩,
    ⟨21, 25, 4, 44885101023⟩,
    ⟨26, 29, 4, 46075577215⟩,
    ⟨30, 33, 4, 48158910551⟩,
    ⟨34, 37, 5, 49478354997⟩,
    ⟨38, 41, 5, 50700577221⟩,
    ⟨42, 45, 5, 51772005794⟩,
    ⟨46, 54, 5, 52948750248⟩,
    ⟨55, 65, 5, 54714418014⟩,
    ⟨66, 76, 6, 56569396372⟩,
    ⟨77, 86, 6, 58047231296⟩,
    ⟨87, 101, 6, 59205441507⟩,
    ⟨102, 113, 6, 60681728572⟩,
    ⟨114, 130, 6, 62048135877⟩,
    ⟨131, 153, 7, 63439727577⟩,
    ⟨154, 180, 7, 65071851278⟩,
    ⟨181, 209, 7, 66653078926⟩,
    ⟨210, 237, 7, 68123849868⟩,
    ⟨238, 272, 7, 69378252149⟩,
    ⟨273, 313, 8, 70755760372⟩,
    ⟨314, 365, 8, 72195842919⟩,
    ⟨366, 421, 8, 73706126532⟩,
    ⟨422, 481, 8, 75144228761⟩,
    ⟨482, 553, 8, 76484834138⟩,
    ⟨554, 634, 9, 77878820124⟩,
    ⟨635, 729, 9, 79243799040⟩,
    ⟨730, 834, 9, 80631110893⟩,
    ⟨835, 958, 9, 81978547871⟩,
    ⟨959, 1105, 9, 83348286055⟩,
    ⟨1106, 1269, 10, 84784450761⟩,
    ⟨1270, 1453, 10, 86168594696⟩,
    ⟨1454, 1661, 10, 87522766859⟩,
    ⟨1662, 1913, 10, 88860271373⟩,
    ⟨1914, 2201, 10, 90269228769⟩,
    ⟨2202, 2525, 11, 91678279488⟩,
    ⟨2526, 2905, 11, 93048242808⟩,
    ⟨2906, 3332, 11, 94449403959⟩,
    ⟨3333, 3829, 11, 95820608345⟩,
    ⟨3830, 4396, 11, 97213969920⟩,
    ⟨4397, 5038, 12, 98593944130⟩,
    ⟨5039, 5797, 12, 99957414198⟩,
    ⟨5798, 6660, 12, 101360837942⟩,
    ⟨6661, 7646, 12, 102749074130⟩,
    ⟨7647, 8777, 12, 104125057472⟩,
    ⟨8778, 10073, 13, 105506430410⟩,
    ⟨10074, 11569, 13, 106885038573⟩,
    ⟨11570, 13288, 13, 108270576051⟩,
    ⟨13289, 15262, 13, 109655338876⟩,
    ⟨15263, 17521, 13, 111040440149⟩,
    ⟨17522, 20118, 14, 112420936661⟩,
    ⟨20119, 23105, 14, 113802112086⟩,
    ⟨23106, 26534, 14, 115187036893⟩,
    ⟨26535, 30465, 14, 116570808110⟩,
    ⟨30466, 34989, 14, 117952577160⟩,
    ⟨34990, 40190, 15, 119336869463⟩,
    ⟨40191, 46144, 15, 120722814528⟩,
    ⟨46145, 52976, 15, 122104241703⟩,
    ⟨52977, 60832, 15, 123485008269⟩,
    ⟨60833, 69861, 15, 124867807525⟩,
    ⟨69862, 80257, 16, 126251687858⟩,
    ⟨80258, 92156, 16, 127638869874⟩,
    ⟨92157, 105818, 16, 129021341399⟩,
    ⟨105819, 121525, 16, 130403721186⟩,
    ⟨121526, 139545, 16, 131787790876⟩,
    ⟨139546, 142300, 17, 131983841862⟩
  ]

end RamareFiniteBounds


