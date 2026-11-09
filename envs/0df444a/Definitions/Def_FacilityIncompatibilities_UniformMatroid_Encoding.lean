-- Prove2me | Definitions.Def_FacilityIncompatibilities_UniformMatroid_Encoding
-- name    : FacilityIncompatibilities_UniformMatroid_Encoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:19:34.929652+00:00
-- url     : https://prove2.me/theorems/8bc5213e-b708-4f5a-8b57-5474752378f6
-- title:
--   §§1–1.2 — rationally encoded uniform-cost instances, input and output words, and the independence oracle
-- statement:
--   For the polynomial-time claim an instance with **uniform opening costs** is given by the numbers $n=|V_C|$ and $m=|V_F|$ (clients $0,\dots,n-1$, facilities $0,\dots,m-1$), the full rational distance table on the $n+m$ points and the common rational opening cost $f$. The **input word** lists $n$ and $m$ in self-delimiting binary, the $(n+m)^2$ table entries in row-major order (clients first, then facilities) and $f$, each rational in lowest terms as a sign bit followed by the binary codes of $|\text{numerator}|$ and of the denominator. Its length $B$ is the binary input length.
--
--   The matroid is not written in the input: it is accessed through the **independence oracle**, which receives the $n$-bit characteristic vector of a client set $X$ and answers whether $X\in\mathcal I$. The **output word** of a solution $(S,\sigma)$ is the $m$-bit characteristic vector of $S$ followed by the binary code of the facility $\sigma(j)$ of every client $j=0,\dots,n-1$.
--
--   These are the input, oracle and output conventions of Theorem 3.
--
--   **Formalization Note** Natural numbers use the published self-delimiting code `QuantumHMMR.natCode`, so the input and output words determine the data. The oracle is a function on bit strings in the published oracle Turing machine model `QAdvFew.PoQOracle.OTM`; a query that is not exactly $n$ bits long is answered `false`. The real FL-MI instance of an encoded instance casts the table to $\mathbb R$ and gives every facility the opening cost $f$.
-- source:
--   Pengfei Wu, Zachary Friggstad, Facility Location with Customer Incompatibilities, STOC 2027 submission #664 (October 2026), SHA-256 e95d28b65476bd15332cddbb49bb8bfb3c370bb260b03d92b35425595cdb7ab3, §1, printed p.2 / PDF p.3 (independence oracles, rational distances); §1.2, printed pp.3–4 / PDF pp.4–5 (rational distances and opening costs)

import Mathlib
import Definitions.Def_FacilityIncompatibilities_UniformMatroid_Model
import Definitions.Def_QuantumHMMR_natListCode
import Definitions.Def_QAdvFew_PoQOracle_OTM

namespace FacilityIncompatibilities.UniformMatroid

/-- **A rationally encoded FL-MI instance with uniform opening costs** (§1, printed p.2, and
§1.2, printed pp.3–4: "rational distances and opening costs"): `n` clients `Fin n`, `m`
facilities `Fin m`, the full rational distance table on `Fin n ⊕ Fin m`, and the common opening
cost `f` of every facility. The matroid is not part of the input: it is accessed through an
independence oracle (`indepOracle`). -/
structure EncodedInstance where
  /-- number of clients -/
  n : ℕ
  /-- number of facilities -/
  m : ℕ
  /-- rational distance table on clients ⊕ facilities -/
  d : Fin n ⊕ Fin m → Fin n ⊕ Fin m → ℚ
  /-- the common (uniform) opening cost -/
  f : ℚ

namespace EncodedInstance

/-- The real FL-MI instance of an encoded instance together with a client matroid `M`:
distances cast to `ℝ`, every facility with opening cost `f`. -/
def toInstance (E : EncodedInstance) (M : Matroid (Fin E.n)) : Instance (Fin E.n) (Fin E.m) where
  d x y := (E.d x y : ℝ)
  f _ := (E.f : ℝ)
  M := M

end EncodedInstance

/-- Binary code of a rational number in lowest terms: a sign bit, then the self-delimiting binary
codes (`QuantumHMMR.natCode`) of `|numerator|` and of the positive denominator. -/
def ratCode (q : ℚ) : List Bool :=
  [decide (q < 0)] ++ QuantumHMMR.natCode q.num.natAbs ++ QuantumHMMR.natCode q.den

/-- **The input word** of an encoded instance: `n` and `m` in self-delimiting binary, the
`(n + m)²` entries of the distance table in row-major order (points numbered by
`finSumFinEquiv`: clients `0, …, n−1`, then facilities `n, …, n+m−1`), then the opening cost `f`.
Its length is the binary input length `B` of the polynomial-time claim. -/
def encode (E : EncodedInstance) : List Bool :=
  QuantumHMMR.natCode E.n ++ QuantumHMMR.natCode E.m ++
    ((List.finRange (E.n + E.m)).flatMap fun a => (List.finRange (E.n + E.m)).flatMap fun b =>
      ratCode (E.d (finSumFinEquiv.symm a) (finSumFinEquiv.symm b))) ++
    ratCode E.f

/-- **The output word** of a solution `(S, σ)`: the characteristic vector of `S ⊆ Fin m`
(`m` bits), followed by the self-delimiting binary code of the facility index `σ(j)` of every
client `j = 0, …, n−1`. -/
def encodeSolution {n m : ℕ} (S : Finset (Fin m)) (σ : Fin n → Fin m) : List Bool :=
  (List.finRange m).map (fun i => decide (i ∈ S)) ++
    (List.finRange n).flatMap fun j => QuantumHMMR.natCode (σ j).val

open Classical in
/-- **The independence oracle** of a matroid `M` on `Fin n` (§1, printed p.2: "given a subset
`X ⊆ V_C` we are able to tell if `X ∈ ℐ`"): a query is the `n`-bit characteristic vector `w` of
`X = {j : w_j = 1}`, and the answer is the exact bit `[X ∈ ℐ]`. A query that is not of length `n`
is answered `false`.

**Formalization Note** The oracle machine (`QAdvFew.PoQOracle.OTM`) pays one step per answer;
writing the query on the query tape is paid by the machine's ordinary steps. -/
noncomputable def indepOracle {n : ℕ} (M : Matroid (Fin n)) : QAdvFew.PoQOracle.Oracle :=
  fun w => decide (w.length = n ∧ M.Indep {j : Fin n | w.getD j.val false = true})

end FacilityIncompatibilities.UniformMatroid


