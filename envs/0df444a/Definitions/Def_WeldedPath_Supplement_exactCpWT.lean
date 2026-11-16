-- Prove2me | Definitions.Def_WeldedPath_Supplement_exactCpWT
-- name    : WeldedPath_Supplement_exactCpWT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:12:51.693826+00:00
-- url     : https://prove2.me/theorems/fec0a87f-b0d5-438f-a7b9-87f643719953
-- title:
--   The exact compressed welded trees oracle $\widehat{\mathrm{cpWT}}$ (Definition 3.6)
-- statement:
--   The welded trees oracle can be evaluated as five permutation queries, $\sigma_{\mathrm{label}}^{-1}\cdot\sigma_b\cdot\sigma_{\mathrm{label}}\cdot\sigma_b\cdot\sigma_{\mathrm{label}}^{-1}$, written out on a work register $Z=(v,f)$. On a query $|l,\alpha\rangle$ the intermediate oracle $O^{wt}_\circ$:
--
--   1. writes $v=\sigma_{\mathrm{label}}^{-1}(l)$ into $Z$;
--   2. for $e=e_\alpha(v)$ with $b=b_{\mathrm{edge}}(e)\in B_{\mathrm{edge}}$, writes $f=\sigma_b(e)$ if $v=\mathrm{tail}(e)$ and $f=\sigma_b^{-1}(e)$ if $v=\mathrm{head}(e)$ (otherwise $f=\bot$; $\bot$ is encoded by $0$, valid edges by nonzero strings);
--   3. lets $w=\mathrm{Nb}_{\sigma_{\mathrm{edge}}}(v,\alpha)$, a function of $(v,\alpha,f)$;
--   4. XORs $\sigma_{\mathrm{label}}(w)$ into $Y$;
--   5. uncomputes $f$, then $v$,
--
--   with the conventions: for $l=0$ the inverse-label calls are skipped and $v=0$; if $l\neq0$ and $v=0$ the middle computation is skipped; if a permuted edge query returns $f=\bot$ then $w=\bot$ and the forward-label step is skipped; if $w=v$ the label $l$ is XORed directly, and if $w=0$ nothing is done; invalid vertices and missing colors have $w=v$; invalid edge values count as $f=\bot$.
--
--   $\widehat{\mathrm{cpWT}}_\circ$ is this computation with each permutation query replaced by the exact compressed query $\widehat{\mathrm{cpO}}$ of Lemma 2.8 on the label database $L$ or the edge database $C_b$, and with $I_Z|\psi\rangle=|\psi\rangle|0,0\rangle_Z$,
--   $$
--   \widehat{\mathrm{cpWT}}=I_Z^\dagger\cdot\widehat{\mathrm{cpWT}}_\circ\cdot I_Z .
--   $$
--   By Observation 3.7 of the source it represents the welded trees oracle exactly on the database registers; Algorithm 3.10 (the probability $p_{\mathrm{cross}}$) runs an algorithm against it.
--
--   **Formalization Note** The five queries are coherently controlled exact queries: the inverse-label query on $(v,L)$ controlled by $l$, the edge query on $(f,C_b)$ controlled by $(l,\alpha,v)$, the forward-label query on $(Y,L)$ controlled by $(l,\alpha,v,f)$; every "skip" or "do nothing" is the identity on that control branch. The exact query is the published construction $\mathcal I_sO_x\mathcal I_s^\dagger+(1-\Pi_{K_s})\mathrm{cpO}_x(1-\Pi_{K_s})$ with the answer written as the label $1,\dots,M$ (label permutation) or as the nonzero edge index $j+1$ (edge permutations); the published `exactCpO` writes the $0$-based value. $v$ and $f$ are $(2n+1)$-bit strings.
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, arXiv:2611.05912 (sha256 b31400a0…), §3.2, O^wt_∘, conventions and Definition 3.6, pp.19–20; Lemma 2.8, (14), p.12

import Mathlib
import Definitions.Def_WeldedPath_exactCpO
import Definitions.Def_WeldedPath_Supplement_cpWT

namespace WeldedPath

namespace Supplement

open QAlgorithms WeldedInstance InjDb

variable {n : ℕ}

/-! ### Exact permutation queries with a prescribed answer encoding -/

/-- The standard query `O_x|a, ϕ⟩ = |a ⊕ enc(ϕ(x)), ϕ⟩` (`inv = false`) or
`|a ⊕ enc(ϕ^{-1}(x)), ϕ⟩` (`inv = true`) (Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder,
arXiv:2611.05912 (sha256 b31400a0…), p.12), the answer `y ∈ [s]` written as the string `enc y`.

**Formalization Note.** The published `stdQuery` is the case `enc = encode d` (the 0-based value
of `y`). Here the answer must be the number the source writes into the work register: a label
`y + 1 ∈ [M]` for the label permutation, a nonzero edge index for an edge permutation (p.19:
"We encode `⊥` by `0` and all valid edge indices by nonzero strings"). -/
noncomputable def stdQueryE {s d : ℕ} (enc : Fin s → Qubits d) (x : Fin s) (inv : Bool) :
    Hil (Qubits d × Equiv.Perm (Fin s)) →L[ℂ] Hil (Qubits d × Equiv.Perm (Fin s)) :=
  basisMap fun p => (p.1 + enc (if inv then p.2.symm x else p.2 x), p.2)

/-- The extended purified oracle `P` for a fixed query `x` with answer encoding `enc`
(arXiv:2611.05912 (sha256 b31400a0…), p.11): `|a⟩|I⟩ ↦ |a ⊕ enc(I(x))⟩|I⟩` if `x ∈ Dom(I)`, the
identity otherwise; the published `purifiedXor` is the case `enc = encode d`. -/
noncomputable def purifiedXorE {s d : ℕ} (enc : Fin s → Qubits d) (x : Fin s) :
    Hil (Qubits d × InjDb s) →L[ℂ] Hil (Qubits d × InjDb s) :=
  basisMap fun p => match p.2 x with
    | some y => (p.1 + enc y, p.2)
    | none => p

/-- The ordinary compressed permutation query `cpO_x` (8) with answer encoding `enc`
(arXiv:2611.05912 (sha256 b31400a0…), p.11): `pC·P·pC†` (forward) and `F·pC·P·pC†·F†` (inverse),
exactly as the published `cpO` with `purifiedXorE enc` in place of `purifiedXor`. -/
noncomputable def cpOE {s d : ℕ} (enc : Fin s → Qubits d) (x : Fin s) (inv : Bool) :
    Hil (Qubits d × InjDb s) →L[ℂ] Hil (Qubits d × InjDb s) :=
  let pc : Hil (Qubits d × InjDb s) →L[ℂ] Hil (Qubits d × InjDb s) := opTensor 1 (pC s x)
  let core := pc.comp ((purifiedXorE enc x).comp (ContinuousLinearMap.adjoint pc))
  let fl : Hil (Qubits d × InjDb s) →L[ℂ] Hil (Qubits d × InjDb s) := opTensor 1 (flipDb s)
  if inv then fl.comp (core.comp (ContinuousLinearMap.adjoint fl)) else core

/-- The exact compressed permutation query (14) of Lemma 2.8 with answer encoding `enc`
(arXiv:2611.05912 (sha256 b31400a0…), p.12): `ĉpO_x = I_s O_x I_s† + (1 − Π_{K_s}) cpO_x (1 − Π_{K_s})`,
`Π_{K_s} = I_s I_s†`, with the published intertwiner `I_s`; the published `exactCpO` is the case
`enc = encode d`. -/
noncomputable def exactCpOE {s d : ℕ} (enc : Fin s → Qubits d) (x : Fin s) (inv : Bool) :
    Hil (Qubits d × InjDb s) →L[ℂ] Hil (Qubits d × InjDb s) :=
  let Is : Hil (Qubits d × Equiv.Perm (Fin s)) →L[ℂ] Hil (Qubits d × InjDb s) :=
    opTensor 1 (intertwiner s)
  let piK := Is.comp (ContinuousLinearMap.adjoint Is)
  Is.comp ((stdQueryE enc x inv).comp (ContinuousLinearMap.adjoint Is)) +
    (1 - piK).comp ((cpOE enc x inv).comp (1 - piK))

/-! ### The work register `Z = (v, f)` -/

/-- The intermediate computation register `Z = (v, f)` of `O^{wt}_∘` (arXiv:2611.05912
(sha256 b31400a0…), p.19): `v` holds a label/vertex value in `[0, M]`, `f` an edge index of the
queried class, both as `(2n+1)`-bit strings.

**Formalization Note.** `v = σ_label^{-1}(l) ∈ [0, M]` fits in `2n + 1` bits. An edge `j` (0-based
in the enumeration `edgeIdx`) of a class is written in `f` as the number `j + 1`, so `⊥` is `0`
(p.19); `|E_b| < |V_n| ≤ 2^{2n+1}`. -/
abbrev ZReg (n : ℕ) := Qubits (2 * n + 1) × Qubits (2 * n + 1)

/-- The answer encoding of the label permutation: `y ∈ [M]` (index `y` of `Fin M`) is written as
the `(2n+1)`-bit string of the number `y + 1`. -/
def encLabel (n : ℕ) (y : Fin (labelBound n)) : Qubits (2 * n + 1) :=
  natToBits (2 * n + 1) (y.1 + 1)

/-- The answer encoding of an edge permutation: the edge with index `j` is written as the
`(2n+1)`-bit string of the nonzero number `j + 1`. -/
def encEdge (n s : ℕ) (j : Fin s) : Qubits (2 * n + 1) := natToBits (2 * n + 1) (j.1 + 1)

/-- The basis states of `X ⊗ Y ⊗ L ⊗ C ⊗ Z`. -/
abbrev FullReg (l : ℕ) (G : WeldedInstance n) := (QReg n × Db l G) × ZReg n

/-- Decidable equality of the basis states of `X ⊗ Y ⊗ L ⊗ C ⊗ Z`. -/
instance instDecEqFull (l : ℕ) (G : WeldedInstance n) : DecidableEq (FullReg l G) :=
  instDecidableEqProd

/-- The neighbor `w = Nb_{σ_edge}(v, α)` as a function of `(v, α, f)` (arXiv:2611.05912
(sha256 b31400a0…), p.19, step 3, and the conventions of p.20), for `e = e_α(v)`:
`v` if `v ∉ V_n` or `e = ⊥` ("invalid structural vertices and missing colors have `w = v`");
`head(e)` / `tail(e)` if `b_edge(e) = ⊥` and `v = tail(e)` / `v = head(e)`; if
`b = b_edge(e) ∈ B_edge` and `f` encodes an edge `g ∈ E_b`, `head(g)` if `v = tail(e)` and
`tail(g)` if `v = head(e)`; `⊥` (`none`) if `b ∈ B_edge` and `f` is `0` or an invalid edge value
("invalid edge-work values are treated as `f = ⊥`", and then "`w = ⊥`"). -/
noncomputable def wOf (l : ℕ) (G : WeldedInstance n) (v : ℕ) (α : Fin 3) (f : ℕ) : Option ℕ :=
  if ¬ IsVertex n v then some v
  else
    match G.eAlpha v α with
    | none => some v
    | some e =>
      match permData l G v α with
      | some ⟨b, _, isTail⟩ =>
        if h : 1 ≤ f ∧ f ≤ classSize l G b then
          let g := ((edgeIdx l G b).symm ⟨f - 1, by omega⟩).1
          some (if isTail then g.head n else g.tail)
        else none
      | none =>
        if G.bEdge l e = none then
          (if v = e.tail then some (e.head n) else if v = e.head n then some e.tail else some v)
        else some v

/-- Step 1/5 of `\widehat{cpWT}_∘`, the exact inverse-label query `\widehat{cpO}^{inv}_lab`
(arXiv:2611.05912 (sha256 b31400a0…), pp.19–20): controlled on the queried label `l`, apply the
exact query `ĉpO` for `σ_label^{-1}(l)` (Lemma 2.8, inverse direction) to the register pair
`(v, L)`, XORing the answer into `v`. For `l = 0` the inverse-label calls are skipped (`v` stays
`0`, p.20); for `l > M` the oracle is the identity (p.17). -/
noncomputable def stepInvLab (l : ℕ) (G : WeldedInstance n) :
    Hil (FullReg l G) →L[ℂ] Hil (FullReg l G) :=
  ofBasis fun p =>
    match toIdx n (bitsToNat p.1.1.1.1) with
    | some x =>
      partImg (exactCpOE (encLabel n) x true) (p.2.1, p.1.2.1)
        fun q => ((p.1.1, (q.2, p.1.2.2)), (q.1, p.2.2))
    | none => ket p

/-- Step 2/5 (and 4/5) of `\widehat{cpWT}_∘`, the exact edge query `\widehat{cpO}_edge`
(arXiv:2611.05912 (sha256 b31400a0…), pp.19–20): controlled on `(l, α, v)`, for `e = e_α(v)` with
`b = b_edge(e) ∈ B_edge`, apply the exact query `ĉpO` for `σ_b(e)` (if `v = tail(e)`) or
`σ_b^{-1}(e)` (if `v = head(e)`) to the register pair `(f, C_b)`, XORing the answer into `f`.
The identity when `l ≠ 0` and `v = 0` ("skip the middle computation", p.20), when `v ∉ V_n`, when
`e_α(v) = ⊥`, and when `b_edge(e) = ⊥` (no permutation is queried, `f = ⊥`). -/
noncomputable def stepEdge (l : ℕ) (G : WeldedInstance n) :
    Hil (FullReg l G) →L[ℂ] Hil (FullReg l G) :=
  ofBasis fun p =>
    let x := bitsToNat p.1.1.1.1
    let v := bitsToNat p.2.1
    if x ≠ 0 ∧ v = 0 then ket p
    else
      match permData l G v p.1.1.1.2 with
      | some ⟨b, e, isTail⟩ =>
        partImg (exactCpOE (encEdge n (classSize l G b)) (edgeIdx l G b e) (!isTail))
          (p.2.2, p.1.2.2 b)
          fun q => ((p.1.1, (p.1.2.1, Function.update p.1.2.2 b q.2)), (p.2.1, q.1))
      | none => ket p

/-- Step 3/5 of `\widehat{cpWT}_∘`, the exact forward-label query `\widehat{cpO}^{for}_lab`
(arXiv:2611.05912 (sha256 b31400a0…), pp.19–20, steps 3–4 and the conventions of p.20):
controlled on `(l, α, v, f)` with `w = wOf(v, α, f)`:
1. `l ≠ 0` and `v = 0`: identity (the middle computation is skipped);
2. `w = ⊥`: identity (the forward-label step is skipped);
3. `w = v`: XOR the original label `l` into `Y`;
4. `w = 0`: identity ("do nothing");
5. otherwise apply the exact query `ĉpO` for `σ_label(w)` (Lemma 2.8, forward) to `(Y, L)`,
   XORing the label into `Y`. -/
noncomputable def stepForLab (l : ℕ) (G : WeldedInstance n) :
    Hil (FullReg l G) →L[ℂ] Hil (FullReg l G) :=
  ofBasis fun p =>
    let x := bitsToNat p.1.1.1.1
    let v := bitsToNat p.2.1
    if x ≠ 0 ∧ v = 0 then ket p
    else
      match wOf l G v p.1.1.1.2 (bitsToNat p.2.2) with
      | none => ket p
      | some w =>
        if w = v then ket (((p.1.1.1, p.1.1.2 + natToBits (2 * n + 1) x), p.1.2), p.2)
        else if w = 0 then ket p
        else
          match toIdx n w with
          | some i =>
            partImg (exactCpOE (encLabel n) i false) (p.1.1.2, p.1.2.1)
              fun q => (((p.1.1.1, q.1), (q.2, p.1.2.2)), p.2)
          | none => ket p

/-- `\widehat{cpWT}_∘ = \widehat{cpO}^{inv}_lab · \widehat{cpO}_edge · \widehat{cpO}^{for}_lab ·
\widehat{cpO}_edge · \widehat{cpO}^{inv}_lab` (arXiv:2611.05912 (sha256 b31400a0…), p.20 and
Definition 3.6): `cpWT_∘` with each permutation query replaced by its exact database query from
Lemma 2.8. -/
noncomputable def exactCpWTCirc (l : ℕ) (G : WeldedInstance n) :
    Hil (FullReg l G) →L[ℂ] Hil (FullReg l G) :=
  (stepInvLab l G).comp ((stepEdge l G).comp ((stepForLab l G).comp
    ((stepEdge l G).comp (stepInvLab l G))))

/-- The isometry `I_Z|ψ⟩ = |ψ⟩|0, 0⟩_Z` (arXiv:2611.05912 (sha256 b31400a0…), Definition 3.6,
p.20). -/
noncomputable def isoZ (l : ℕ) (G : WeldedInstance n) :
    Hil (QReg n × Db l G) →L[ℂ] Hil (FullReg l G) :=
  ofBasis fun p => ket (p, ((0 : Qubits (2 * n + 1)), (0 : Qubits (2 * n + 1))))

/-- The exact compressed welded trees oracle (Definition 3.6; arXiv:2611.05912
(sha256 b31400a0…), p.20): `\widehat{cpWT} := I_Z† · \widehat{cpWT}_∘ · I_Z`, an operator on
`X ⊗ Y ⊗ L ⊗ C`.

**Formalization Note.**
1. The five queries are the exact queries `ĉpO` of Lemma 2.8 (`exactCpOE`: the published
   construction from the intertwiner `I_s`, with the answer written as a label `1, …, M` or a
   nonzero edge index), coherently controlled on the registers that name them: `l` for the
   inverse-label query on `L`; `(l, α, v)` for the edge query on `C_b`, `b = b_edge(e_α(v))`;
   `(l, α, v, f)` for the forward-label query on `L`.
2. Each convention of p.20 ("skip", "do nothing") is the identity on that control branch;
   "XOR the original label `l` directly" XORs the string of `l` into `Y`.
3. `Z = (v, f)` is two `(2n+1)`-bit strings, `⊥` is `0`, the edge `j` of a class is `j + 1`. -/
noncomputable def exactCpWT (l : ℕ) (G : WeldedInstance n) :
    Hil (QReg n × Db l G) →L[ℂ] Hil (QReg n × Db l G) :=
  (ContinuousLinearMap.adjoint (isoZ l G)).comp ((exactCpWTCirc l G).comp (isoZ l G))

end Supplement

end WeldedPath


