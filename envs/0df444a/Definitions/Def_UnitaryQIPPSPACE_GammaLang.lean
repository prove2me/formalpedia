-- Prove2me | Definitions.Def_UnitaryQIPPSPACE_GammaLang
-- name    : UnitaryQIPPSPACE_GammaLang
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:28:18.18148+00:00
-- url     : https://prove2.me/theorems/3d8e4bc0-1ff1-4813-b35d-168f9c928d4c
-- title:
--   The correction language $\Gamma_A$ (Lemma 4.13)
-- statement:
--   For a language $A$ and a string $x=(y,t)$ with last bit $t$, $h_A(y,t)=t\cdot A(y)$. For a list $a_{\le j}=(a_1,\dots,a_j)$ of strings of length $|x|$ and $S\subseteq[j]$, $a_S=\bigoplus_{i\in S}a_i$ (with $a_\emptyset=0^{|x|}$), and
--   $$\Gamma_A(a_{\le j},x):=\bigoplus_{S\subseteq[j]}h_A(x\oplus a_S),$$
--   with $\Gamma_A=0$ on illegitimate input.
--
--   By the iterated-difference formula, $\Gamma_A(z_j,\cdot)$ is the correction function required in round $j$ of the injection for a query to $A$.
--
--   **Formalization Note** The pair $(a_{\le j},x)$ is encoded as $\mathrm{tup}[\mathrm{tup}[a_1,\dots,a_j],x]$, the list as one string $z$, the format in which Lemma 4.16 and Protocol 4.17 pass $(z,x)$. Illegitimate input: anything else, $|x|=0$, or some $a_i$ of the wrong length.
-- source:
--   He, Ou, Zhao, unitaryQIP = unitaryPSPACE, arXiv:2611.02819 (held version, sha256 9e357a00…ead793), Lemma 4.13, p.29 (PDF p.31)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity
import Definitions.Def_QAdvFew_PoQOracle_tup

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace UnitaryQIPPSPACE

/-- Bitwise XOR of two bit strings (of equal length in every use). -/
def strXor (x y : Str) : Str := List.zipWith Bool.xor x y

/-- `h_A(y, t) = t · A(y)` for a bit string `x = (y, t)` with last bit `t` (Lemma 4.13, p. 29);
`false` on the empty string. -/
def hLang (A : Set Str) (x : Str) : Prop := x.getLast? = some true ∧ x.dropLast ∈ A

/-- `a_S := ⊕_{i ∈ S} a_i` for a list `a = (a₁, …, a_j)` of strings of length `L` and `S ⊆ [j]`,
with `a_∅ = 0^L`. -/
def strXorSet (L : ℕ) (as : List Str) (S : Finset (Fin as.length)) : Str :=
  (List.finRange as.length).foldl (fun acc i => if i ∈ S then strXor acc (as.get i) else acc)
    (List.replicate L false)

open Classical in
/-- **The correction language `Γ_A`** (He, Ou, Zhao, *unitaryQIP = unitaryPSPACE*,
arXiv:2611.02819, held version sha256 9e357a00…, Lemma 4.13, p. 29 (PDF p. 31)): "For a bitstring
`x` with `|x| = ℓ + 1`, we split `x = (y, t)` with `y ∈ {0,1}^ℓ` and `t ∈ {0,1}`, and define
`h_A(y, t) = t · A(y)`. For `j ≥ 0` and a list `a_{≤j} = (a₁, …, a_j)` of `j` strings of length `|x|`
(empty if `j = 0`), implicitly encoded as a binary string, write `a_S := ⊕_{i ∈ S} a_i` for
`S ⊆ [j]`, with `a_∅ = 0^{|x|}`. We define the language `Γ_A(a_{≤j}, x) := ⊕_{S ⊆ [j]} h_A(x ⊕ a_S)`,
and we set `Γ_A = 0` on illegitimate input."

Encoding: the pair `(a_{≤j}, x)` is the string `tup [tup [a₁, …, a_j], x]` (the list encoded as the
string `z = tup [a₁, …, a_j]`, the format in which Lemma 4.16 and Protocol 4.17 pass `(z, x)`). A
string is in `Γ_A` iff it has this form with `|x| ≥ 1`, every `a_i` of length `|x|`, and an odd
number of subsets `S ⊆ [j]` with `h_A(x ⊕ a_S) = 1`. Every other string ("illegitimate input") is
not in `Γ_A`. -/
def GammaLang (A : Set Str) : Set Str :=
  {s | ∃ (as : List Str) (x : Str), s = tup [tup as, x] ∧ x ≠ [] ∧
    (∀ a ∈ as, a.length = x.length) ∧
    Odd (Finset.univ.filter fun S : Finset (Fin as.length) =>
      hLang A (strXor x (strXorSet x.length as S))).card}

end UnitaryQIPPSPACE


