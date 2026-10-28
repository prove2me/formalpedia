-- Prove2me | Definitions.Def_BitcoinActivation
-- name    : BitcoinActivation
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-10-26T04:14:01.068987+00:00
-- url     : https://prove2.me/theorems/48a6cddb-c8aa-4658-be2a-4c44f097e574
-- title:
--   Buried deployments, script-verification flags by height, and the two exception blocks
-- statement:
--   A **buried deployment** is one of `HEIGHTINCB` (BIP34), `CLTV` (BIP65), `DERSIG` (BIP66), `CSV`, `SEGWIT`, with mainnet activation heights $227{,}931$, $388{,}381$, $363{,}725$, $419{,}328$, $481{,}824$ (`deploymentHeight`). `activeAt`(height, dep) holds when the deployment height is at most the block height, as `DeploymentActiveAt`; `activeAfter`(prevHeight, dep) holds when it is at most prevHeight $+ 1$, as `DeploymentActiveAfter`.
--
--   A **flag set** is a record of seven Booleans: `p2sh`, `witness`, `taproot`, `dersig`, `cltv`, `csv`, `nulldummy`. `noFlags` has none; `baseFlags` has `p2sh`, `witness`, `taproot`. A block's **exception status** is `none`, `bip16Block` (the hash-keyed P2SH violation) or `taprootBlock` (the hash-keyed Taproot violation); `exceptionBase` yields `baseFlags`, `noFlags`, and `p2sh`+`witness` respectively.
--
--   `blockScriptFlags`(height, exc) is `GetBlockScriptFlags`: the exception base, with `dersig`, `cltv`, `csv`, `nulldummy` each OR-ed with `activeAt` of `DERSIG`, `CLTV`, `CSV`, `SEGWIT` at the height. `ScriptFlags.le` is pointwise inclusion: every flag true in the first is true in the second.
--
--   $\mathrm{LOCKTIME\_VERIFY\_SEQUENCE} = 1$, and `lockTimeFlags`(height) is that value when `CSV` is active at the height and $0$ otherwise, as `nLockTimeFlags` in `ConnectBlock`.
--
--   **Formalization Note.** The exception table is modeled by the three-valued classification rather than a hash lookup. Versionbits deployments are not modeled, since the pinned source consults none for mainnet consensus flags. Only `Std` is imported.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: GetBlockScriptFlags, src/validation.cpp lines 2249-2288: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp#L2249; DeploymentActiveAt / DeploymentActiveAfter (buried), src/deploymentstatus.h; BuriedDeployment and DeploymentHeight, src/consensus/params.h; CMainParams BIP34Height, BIP65Height, BIP66Height, CSVHeight, SegwitHeight, script_flag_exceptions, src/kernel/chainparams.cpp; LOCKTIME_VERIFY_SEQUENCE, src/consensus/consensus.h; nLockTimeFlags in ConnectBlock, src/validation.cpp line 2478

import Std

namespace BitcoinActivation

/-! Transcription of the historical rule selection of Bitcoin Core at revision
`a773e1e33b349dc819b5a0edc1c7a4839dc73b48`: the buried deployment heights of `CMainParams`
(`kernel/chainparams.cpp`), `DeploymentActiveAt` / `DeploymentActiveAfter` for buried deployments
(`deploymentstatus.h`), `GetBlockScriptFlags` with the two `script_flag_exceptions`
(`validation.cpp`), and the `nLockTimeFlags` selection in `ConnectBlock`. -/

/-- `Consensus::BuriedDeployment`. -/
inductive BuriedDeployment where
  | heightInCB   -- BIP34
  | cltv         -- BIP65
  | derSig       -- BIP66
  | csv          -- BIP68/112/113
  | segwit       -- BIP141/143/147
  deriving DecidableEq, Repr

/-- `Consensus::Params::DeploymentHeight` at mainnet values. -/
def deploymentHeight : BuriedDeployment → Nat
  | .heightInCB => 227931
  | .cltv => 388381
  | .derSig => 363725
  | .csv => 419328
  | .segwit => 481824

/-- `DeploymentActiveAt(index, dep) = index.nHeight >= DeploymentHeight(dep)`. -/
def activeAt (height : Nat) (dep : BuriedDeployment) : Bool := decide (deploymentHeight dep ≤ height)

/-- `DeploymentActiveAfter(pindexPrev, dep) = pindexPrev->nHeight + 1 >= DeploymentHeight(dep)`. -/
def activeAfter (prevHeight : Nat) (dep : BuriedDeployment) : Bool :=
  decide (deploymentHeight dep ≤ prevHeight + 1)

/-- The consensus script-verification flags `GetBlockScriptFlags` can set. -/
structure ScriptFlags where
  p2sh : Bool
  witness : Bool
  taproot : Bool
  dersig : Bool
  cltv : Bool
  csv : Bool
  nulldummy : Bool
  deriving DecidableEq, Repr

/-- `SCRIPT_VERIFY_NONE`. -/
def noFlags : ScriptFlags := ⟨false, false, false, false, false, false, false⟩

/-- The default base `SCRIPT_VERIFY_P2SH | SCRIPT_VERIFY_WITNESS | SCRIPT_VERIFY_TAPROOT`. -/
def baseFlags : ScriptFlags := ⟨true, true, true, false, false, false, false⟩

/-- `consensus.script_flag_exceptions`: the block is one of the two historical exceptions, or
not. The BIP16 exception (`00000000000002dc…9c22`) maps to `SCRIPT_VERIFY_NONE`; the Taproot
exception (`0000000000000000000f14c3…95ad`) maps to `SCRIPT_VERIFY_P2SH | SCRIPT_VERIFY_WITNESS`. -/
inductive ScriptException where
  | none
  | bip16Block
  | taprootBlock
  deriving DecidableEq, Repr

/-- The flags the exception table yields, or the default base. -/
def exceptionBase : ScriptException → ScriptFlags
  | .none => baseFlags
  | .bip16Block => noFlags
  | .taprootBlock => ⟨true, true, false, false, false, false, false⟩

/-- `GetBlockScriptFlags(block_index)` at mainnet: the base (default or exception), then
`DERSIG`, `CHECKLOCKTIMEVERIFY`, `CHECKSEQUENCEVERIFY` and `NULLDUMMY` added when BIP66, BIP65,
CSV and SegWit respectively are active at the block's height. -/
def blockScriptFlags (height : Nat) (exc : ScriptException) : ScriptFlags :=
  let f := exceptionBase exc
  { f with
    dersig := f.dersig || activeAt height .derSig
    cltv := f.cltv || activeAt height .cltv
    csv := f.csv || activeAt height .csv
    nulldummy := f.nulldummy || activeAt height .segwit }

/-- Pointwise inclusion of flag sets: every rule enforced by the first is enforced by the second. -/
def ScriptFlags.le (a b : ScriptFlags) : Prop :=
  (a.p2sh = true → b.p2sh = true) ∧ (a.witness = true → b.witness = true) ∧
  (a.taproot = true → b.taproot = true) ∧ (a.dersig = true → b.dersig = true) ∧
  (a.cltv = true → b.cltv = true) ∧ (a.csv = true → b.csv = true) ∧
  (a.nulldummy = true → b.nulldummy = true)

/-- `consensus/consensus.h`: `LOCKTIME_VERIFY_SEQUENCE = (1 << 0)`. -/
def LOCKTIME_VERIFY_SEQUENCE : Nat := 1

/-- The `nLockTimeFlags` of `ConnectBlock`: `LOCKTIME_VERIFY_SEQUENCE` once CSV is active at the
block's height, else `0`. -/
def lockTimeFlags (height : Nat) : Nat :=
  if activeAt height .csv then LOCKTIME_VERIFY_SEQUENCE else 0

end BitcoinActivation


