-- Prove2me | Definitions.Def_LockingAccInfo_keyEnsemble
-- name    : LockingAccInfo_keyEnsemble
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:41:56.704999+00:00
-- url     : https://prove2.me/theorems/0d4e14e4-fd2f-4202-ab94-2b6cf2b170ca
-- title:
--   The $n$-bit key $S$ with $\rho_{S_n f(S_1,\dots,S_{n-1})E}=\rho_{XYE}$ (§IV)
-- statement:
--   Let $g:\mathcal Y=\{1,2,3\}^m\to\{0,1\}^{n-1}$ be injective. The $n$-bit key $S=(S_1,\dots,S_n)$ is $S=(g(Y),X)$: its first $n-1$ bits encode $Y$, its last bit is $X$, and $E$ is the system of §III. Thus
--
--   $$
--   P_S(s',x)=\begin{cases}\frac1{2\cdot3^m}, & s'=g(y)\text{ for some }y,\\ 0,&\text{otherwise,}\end{cases}\qquad \rho_{E|S=(g(y),x)}=\rho_{E|(X,Y)=(x,y)} ,
--   $$
--
--   so that $\rho_{S_n\,f(S_1,\dots,S_{n-1})\,E}=\rho_{XYE}$ with $f=g^{-1}$ on the range of $g$.
--
--   This is the key of the paper's cryptographic example: its accessible information is tiny, yet knowing $S_1,\dots,S_{n-1}$ reveals $S_n$.
--
--   **Formalization Note** The key is the pair (prefix `Fin (n-1) → Bool`, last bit `Bool`). Since $|\{0,1\}^{n-1}|=2^{n-1}\ne3^m$, a bijection $f$ on all of $\{0,1\}^{n-1}$ does not exist (footnote 28: $S$ is not perfectly uniform on the key space); the paper's $f$ is $g^{-1}$ on the range of $g$. Prefixes outside the range have probability $0$, and their conditional state is the completely mixed state $2^{-m}\mathrm{id}$, a placeholder no statement weights. The definition is meant for injective $g$, which every statement assumes.
-- source:
--   König, Renner, Bariska, Maurer, Locking of accessible information and implications for the security of quantum cryptography, arXiv:quant-ph/0512021v2, §IV, p.3, with footnotes 27–28, p.5

import Mathlib
import Definitions.Def_LockingAccInfo_lockState
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P07

open QAlgorithms.Papers.Independent.Dependency50.P07 (CQData)

namespace LockingAccInfo

open Classical in
/-- König, Renner, Bariska, Maurer, arXiv:quant-ph/0512021v2, §IV, p.3, with footnotes 27–28,
p.5: "an n-bit key S = (S1, . . . , Sn) together with a quantum system E controlled by an
adversary such that, for some bijective mapping f, ρ_{Sn f(S1,...,Sn−1)E} = ρXYE", where
"X = Sn and Y = f(S1, . . . , Sn−1)" (footnote 27) and ρXYE is the state of §III, Eq. (3).

**Formalization Note.** The n-bit string S is the pair `(S₁…S_{n−1}, S_n)` of a prefix
`Fin (n-1) → Bool` and a last bit `Bool` (`false` = 0). Since `|{0,1}^{n−1}| = 2^{n−1}` and
`|Y| = 3^m` differ for `m ≥ 1`, no bijection f on all of `{0,1}^{n−1}` exists (footnote 28: "S is
not perfectly uniformly distributed on the key space"); the encoding is an injective map
`g : Y → {0,1}^{n−1}` with `f = g⁻¹` on its range, so `S = (g(Y), X)`. The key value `(s', x)`
has probability `1/(2 · 3^m)` when `s' = g(y)` for some `y` and probability 0 otherwise, and the
state of E given it is `ρE|(X,Y)=(x,y)`. Off the range of `g` (probability 0) the conditional
state is the completely mixed state `2^{−m} id`, a placeholder that no statement weights. The
definition is meant for injective `g`; every statement using it assumes `Function.Injective g`. -/
noncomputable def keyEnsemble {n m : ℕ} (g : (Fin m → Fin 3) → (Fin (n - 1) → Bool)) :
    CQData ((Fin (n - 1) → Bool) × Bool) (Fin m → Fin 2) where
  prob s := if ∃ y, g y = s.1 then ((2 : ℝ) * 3 ^ m)⁻¹ else 0
  state s := if h : ∃ y, g y = s.1 then lockState s.2 (Classical.choose h)
    else ((2 : ℂ) ^ m)⁻¹ • 1

end LockingAccInfo


