-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLocGrecR
-- name    : IntMul_Kappa_R8_Data_BitOppbankLocGrecR
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T11:35:29.952203+00:00
-- url     : https://prove2.me/theorems/a25a5547-2af6-40ef-94f1-d8ca5920df46
-- title:
--   R8 opp-bank corrected densified GREC for variant R (72387 Recs, 283 chunks)
-- statement:
--   # Opp-bank BitNB corrected densified GREC (variant R)
--
--   This is the concatenated packed table of producer records for the densified opp-bank bit network DAG on $n=62478$ nodes. Node identifiers occupy the dense range $0,\ldots,62477$, so the associated node codes
--
--   $$
--   c_{\mathrm{ND}}(n)=1773+n
--   $$
--
--   remain strictly below the flag-basis bound $64251$.
--
--   The table contains $72387$ records, packed into $283$ natural-number chunks with at most $256$ records per chunk, using the same bit layout as the published table $\texttt{IntMul\_Kappa\_R8\_Data\_BitOppbankLocGrecDense}$. It is the concatenation of the two published packs $\texttt{GREC0}$ ($142$ chunks) and $\texttt{GREC1}$ ($141$ chunks). A packed chunk $X\in\mathbb{N}$ stores a record count in its low sixteen bits and a payload in the remaining bits. Writing $c=X\bmod 2^{16}$ and $p=\lfloor X/2^{16}\rfloor$, the chunk decodes as $\mathrm{recsDec}(c,\,p)$.
--
--   This table is the full densified producer DAG used by the variant-R stage-one word. It is not a drop-in replacement for the shorter published LocGrecDense table ($54290$ records, $213$ chunks) consumed by $\texttt{QHNetRec}$.
--
--   **Formalization Note.** The Lean namespace is `IntMul.Kappa.R8.Bit.Oppbank.LocGrecR`. The public constant is $\texttt{GREC}:\mathrm{List}\,\mathbb{N}$, defined as $\texttt{GREC0}+\hspace{-0.2em}+\texttt{GREC1}$. Do not import this module together with a conflicting $\texttt{GREC}$ declaration under the same open namespace.
-- source:
--   Corrected full densified GREC for the variant-R stage-one word, concatenation of IntMul_Kappa_R8_Data_BitOppbankLocGrecR0 (definition_id af79259d-74b0-4f12-9d69-6cd91a8fbac6) and IntMul_Kappa_R8_Data_BitOppbankLocGrecR1 (definition_id 69d98ab3-0fe7-4ad1-98bd-57708999c015). Packing identical to LocGrecDense (definition_id 819da911-7cc1-4823-8d94-32f6972a14ed). Local source: Definitions/Def_IntMul_Kappa_R8_Data_BitOppbankLocGrecR.lean. 72387 Recs, 283 chunks, nNodes=62478. An earlier one-file submission failed the 1 MiB token-scanner limit (job fb9d626e-1c6d-4316-bb5e-d0643ba9ca1a).

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLocGrecR0
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLocGrecR1
import Mathlib.Data.Nat.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R8 Loc GREC for variant R (corrected full densified DAG)

Concatenation of LocGrecR0 and LocGrecR1. chunks=283, packing identical to LocGrecDense.
Node ids are dense `0 .. nNodes-1` so `cND n < codeBound = 64251`.
-/

namespace IntMul.Kappa.R8.Bit.Oppbank.LocGrecR

def nNodes : ℕ := 62478
theorem nNodes_eq : nNodes = 62478 := rfl

def GREC : List ℕ :=
  IntMul.Kappa.R8.Bit.Oppbank.LocGrecR0.GREC0 ++
    IntMul.Kappa.R8.Bit.Oppbank.LocGrecR1.GREC1

theorem grec_chunks_len : GREC.length = 283 := by
  unfold GREC
  rw [List.length_append, LocGrecR0.grec0_chunks_len, LocGrecR1.grec1_chunks_len]

end IntMul.Kappa.R8.Bit.Oppbank.LocGrecR


